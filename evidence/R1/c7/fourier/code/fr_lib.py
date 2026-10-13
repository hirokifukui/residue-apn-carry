"""C7 lane fourier (P7-06/P7-07), Claude 2026-10-12.  Shared helpers.
Read-only import of the AUTHOR arithmetic c5/a1/code/a1c5_lib.py (the same module C6/a1 uses), located
relative to this file (no HOME path).  MOD[3] = 1+t+t^3 is added IN MEMORY ONLY (as C6 a1c6_lib does).
Conventions (a1c5_lib): code x = a | (b << m), a = lo = digit 0 (fibre index), b = hi = digit 1;
PD: F(a,b) = (p(a), h(a) + d(a) b), B = J o F.  Input difference alpha = u + q v, output beta = s + q t.

Formula side (GPT NEW_DERIVATIONS_JA.md section B), implemented here independently of the GPT check:
  k = d(u)+d(0) (= K(u)),  A_a = d(a) d(a+u)/k,
  C_a = h(a) + (d(a)/k)[s + h(a+u) + h(a) + d(a+u)(a AND u)],  D_up(a) = p(a+u)+p(a),
  rhs[eta,xi] = sum_{a : eta = M*_{A_a}(s AND xi)} (-1)^{<xi,D_up(a)> + <s AND xi, C_a>}   (integer, 'count units')
  and the claim  Hhat(block_{u,s}) = q * rhs,  Hhat = Sylvester-Hadamard on v (rows) and t (cols) of the
  integer DDT block C[u+qv, s+qt].  Orthonormal probability-normalised entry That = rhs / q^2.
"""
import os, sys
import numpy as np
P = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
sys.path.insert(0, os.path.join(P, 'c5', 'a1', 'code'))
import a1c5_lib as L5
L5.MOD.setdefault(3, (1, 1, 0, 1))
from a1c5_lib import GF, ring_ops, pd_table, extract_pd, ddt, build_lifts  # noqa: E402


def parity_table(q):
    return np.array([bin(x).count('1') & 1 for x in range(q)], dtype=np.int64)


def wt_table(q):
    return np.array([bin(x).count('1') for x in range(q)], dtype=np.int64)


def adj_table(K):
    """adj[c, x] = M_c^*(x) w.r.t. the coordinate dot product: bit j = <x, c * e_j>."""
    q, m = K.q, K.m; par = parity_table(q); X = np.arange(q)
    adj = np.zeros((q, q), dtype=np.int64)
    for j in range(m):
        adj |= par[K.MUL[:, 1 << j][:, None] & X[None, :]] << j
    return adj


def inv_adj_table(adj):
    """iadj[c, eta] = z with adj[c, z] = eta (c != 0)."""
    q = adj.shape[0]; iadj = np.full((q, q), -1, dtype=np.int64)
    for c in range(1, q):
        iadj[c, adj[c]] = np.arange(q)
    return iadj


def tables(m, nextra=0):
    """Return K and an ordered dict name -> PD code table F (all verified by extract_pd)."""
    K = GF(m); q = K.q; A = np.arange(q)
    inv = K.pow(A, q - 2); a3 = K.pow(A, 3)
    sq = K.MUL[A, A]; d0 = K.MUL[sq, sq] ^ sq ^ 1
    y = K.MUL[A, K.INV[3]]; ys = K.MUL[y, y]; drho = K.MUL[ys, ys] ^ ys ^ 1
    out = {}
    if m == 3:   # same list and seed as C6 a1c6_lib.lifts(3)
        rng = np.random.default_rng(20261011 + 300)
        out['inv_h0'] = pd_table(K, inv, np.zeros(q, np.int64), d0)
        out['inv_ha3'] = pd_table(K, inv, a3, d0)
        out['inv_rho3_hrand'] = pd_table(K, inv, rng.integers(0, q, q), drho)
        out['gold_hrand'] = pd_table(K, a3, rng.integers(0, q, q), d0)
    else:
        lf, _ = build_lifts(K, ('natural', 'inv', 'rho'))
        for k in lf:
            if k.startswith('natural_P') or k in ('inv_ha3', 'inv_rho3_hrand') or k.startswith('gold_rho'):
                out[k] = lf[k]
    rng = np.random.default_rng(70700 + m)
    for i in range(nextra):
        out['inv_d0_hr%d' % i] = pd_table(K, inv, rng.integers(0, q, q), d0)
        out['inv_rho3_hr%d' % i] = pd_table(K, inv, rng.integers(0, q, q), drho)
    for F in out.values():
        extract_pd(K, F)
    return K, out


def fwht2(B):
    """Unnormalised Sylvester-Hadamard on both axes of an integer q x q array: H B H."""
    A = B.astype(np.int64).copy()
    for ax in (0, 1):
        A = np.swapaxes(A, ax, -1); n = A.shape[-1]; h = 1
        while h < n:
            z = A.reshape(*A.shape[:-1], -1, 2 * h)
            x = z[..., :h].copy(); y = z[..., h:].copy()
            z[..., :h] = x + y; z[..., h:] = x - y; h *= 2
        A = np.swapaxes(A, ax, -1)
    return A


class Formula:
    """Formula side for one PD (p,h,d) over K."""
    def __init__(self, K, info):
        self.K = K; self.q = K.q; self.m = K.m
        self.p, self.h, self.d, self.rho = info['p'], info['h'], info['d'], int(info['rho'])
        self.adj = adj_table(K); self.iadj = inv_adj_table(self.adj)
        self.par = parity_table(self.q); self.wt = wt_table(self.q)
        self.G = [u for u in range(1, self.q) if u != self.rho]

    def coeffs(self, u, s):
        K, d, h, p = self.K, self.d, self.h, self.p; a = np.arange(self.q); au = a ^ u
        k = int(d[u] ^ d[0]); assert k != 0
        ik = K.INV[k]
        A = K.MUL[K.MUL[d, d[au]], ik]
        C = h ^ K.MUL[K.MUL[d, ik], s ^ h[au] ^ h ^ K.MUL[d[au], a & u]]
        Dp = p[au] ^ p
        return A, C, Dp

    def atoms(self, u, s):
        """eta[xi,a], chi[xi,a] (+-1) for all xi in F (rows) and a in F (cols)."""
        q = self.q; A, C, Dp = self.coeffs(u, s)
        xi = np.arange(q)[:, None]; z = s & xi
        eta = self.adj[A[None, :], z]
        chi = 1 - 2 * (self.par[xi & Dp[None, :]] ^ self.par[z & C[None, :]])
        return eta, chi

    def rhs(self, u, s):
        q = self.q; eta, chi = self.atoms(u, s)
        idx = (eta * q + np.arange(q)[:, None]).ravel()
        R = np.bincount(idx, weights=chi.ravel(), minlength=q * q).reshape(q, q).astype(np.int64)
        Fb = np.bincount(idx, minlength=q * q).reshape(q, q)
        return R, Fb          # indexed [eta, xi]
