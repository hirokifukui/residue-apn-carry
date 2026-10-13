"""P8-07 core: GF(2^m) in a fixed polynomial basis, PD data, brute DDT of B=J∘F over GR(4,m)
in two-digit coordinates, and the G-block of the partial Fourier transform (formula and brute).
Independent implementation (C8 / P8-07).  Bit i of an int <-> coefficient of t^i.
"""
import numpy as np

IRRED = {3: 0b1011, 5: 0b100101, 7: 0b10000011, 9: 0b1000010001, 11: 0b100000000101}


class Field:
    def __init__(self, m):
        self.m = m
        self.q = q = 1 << m
        f = IRRED[m]
        mul = np.zeros((q, q), dtype=np.int64)
        for x in range(q):
            # row x: x * y for all y, by shift-and-add over the bits of y
            acc = np.zeros(q, dtype=np.int64)
            ys = np.arange(q)
            xx = x
            for j in range(m):
                bit = (ys >> j) & 1
                acc ^= bit * xx
                xx <<= 1
                if xx >> m:
                    xx ^= f
            mul[x] = acc
        self.mul = mul
        inv = np.zeros(q, dtype=np.int64)
        for x in range(1, q):
            inv[x] = int(np.nonzero(mul[x] == 1)[0][0])
        self.inv = inv
        self.par = np.array([bin(i).count("1") & 1 for i in range(q)], dtype=np.int64)
        self.wt = np.array([bin(i).count("1") for i in range(q)], dtype=np.int64)
        idx = np.arange(q)
        self.H = np.where(self.par[idx[:, None] & idx[None, :]] == 1, -1, 1).astype(np.int64)

    def power(self, e):
        q = self.q
        out = np.zeros(q, dtype=np.int64)
        for x in range(q):
            r, b, ee = 1, x, e
            while ee:
                if ee & 1:
                    r = int(self.mul[r, b])
                b = int(self.mul[b, b])
                ee >>= 1
            out[x] = r
        out[0] = 0 if e > 0 else 1
        return out

    def adjT(self, A):
        """array z -> M_A^* z (adjoint of x->A x for the coordinate inner product)."""
        q, m = self.q, self.m
        z = np.arange(q)
        out = np.zeros(q, dtype=np.int64)
        for j in range(m):
            out |= self.par[z & int(self.mul[A, 1 << j])] << j
        return out


def is_apn_perm(F, p):
    q = F.q
    if len(set(p.tolist())) != q:
        return False
    for u in range(1, q):
        D = p[np.arange(q) ^ u] ^ p
        if np.bincount(D, minlength=q).max() > 2:
            return False
    return True


def lin_from_matrix(F, cols):
    """F2-linear map given by images of basis vectors."""
    q, m = F.q, F.m
    x = np.arange(q)
    out = np.zeros(q, dtype=np.int64)
    for j in range(m):
        out ^= ((x >> j) & 1) * cols[j]
    return out


class PD:
    """p APN permutation, d = eps xor K (K linear, ker K={0,rho}, eps notin Im K), h arbitrary."""

    def __init__(self, F, p, K, eps, h):
        self.F = F
        q = F.q
        self.p, self.K, self.eps, self.h = p.astype(np.int64), K.astype(np.int64), int(eps), h.astype(np.int64)
        ker = np.nonzero(self.K == 0)[0]
        assert len(ker) == 2, ker
        self.rho = int(ker[1])
        assert eps not in set(self.K.tolist())
        self.d = self.K ^ self.eps
        assert (self.d != 0).all()
        self.U = [u for u in range(1, q) if u != self.rho]


def d0_K(F, rho=1):
    """K(x)=K0(x/rho), K0(x)=x^4+x^2 ; eps=1 (m odd)."""
    q = F.q
    x = np.arange(q)
    xr = F.mul[x, F.inv[rho]]
    x2 = F.mul[xr, xr]
    x4 = F.mul[x2, x2]
    return x4 ^ x2, 1


def random_K(F, rng, rho=None):
    q, m = F.q, F.m
    while True:
        if rho is None:
            r = int(rng.integers(1, q))
        else:
            r = rho
        cols = rng.integers(0, q, size=m)
        Kr = int(lin_from_matrix(F, cols)[r])
        # theta with <theta,r>=1: lowest set bit of r
        tb = r & (-r)
        Kmap = lin_from_matrix(F, cols)
        x = np.arange(q)
        K = Kmap ^ (((x & tb) != 0).astype(np.int64) * Kr)
        if (K == 0).sum() == 2:
            img = set(K.tolist())
            outs = [e for e in range(q) if e not in img]
            eps = int(rng.choice(outs))
            return K, eps


# ---------------- brute force ----------------
def brute_ddt(P):
    F = P.F
    q = F.q
    N = q * q
    a = np.arange(N) // q
    b = np.arange(N) % q
    Bl = P.h[a] ^ F.mul[P.d[a], b]
    Bh = P.p[a]
    D = np.zeros((N, N), dtype=np.int64)
    for al in range(N):
        u, v = al // q, al % q
        a2 = a ^ u
        b2 = b ^ v ^ (a & u)
        y0, y1 = Bl[a2 * q + b2], Bh[a2 * q + b2]
        z0, z1 = Bl, Bh
        s = y0 ^ z0
        t = y1 ^ z1 ^ (z0 & s)
        D[al] = np.bincount(s * q + t, minlength=N)
    return D


def brute_G(P, D):
    """g_brute[(u,eta),(s,xi)] = q^2 * That on G rows (eta!=0) and xi!=0 columns."""
    F = P.F
    q = F.q
    H = F.H
    D4 = D.reshape(q, q, q, q).astype(np.int64)
    # (1/q) sum_{v,t} H[eta,v] H[xi,t] D[u,v,s,t]
    X = np.einsum('ev,uvst->uest', H, D4)
    X = np.einsum('xt,uest->uesx', H, X)
    assert (X % q == 0).all()
    X //= q
    rows = X[P.U][:, 1:, :, 1:]  # (|U|, q-1, q, q-1)
    return rows.reshape(len(P.U) * (q - 1), q * (q - 1))


# ---------------- formula ----------------
def atoms(P):
    """per atom (u,a): u-index, a, A, mu, y=D_u p(a), Cfun constants (h(a), E_a)."""
    F = P.F
    q = F.q
    out = []
    for ui, u in enumerate(P.U):
        k = int(P.K[u])
        kin = int(F.inv[k])
        for a in range(q):
            mu = int(F.mul[P.d[a], kin])
            A = int(F.mul[mu, P.d[a ^ u]])
            y = int(P.p[a ^ u] ^ P.p[a])
            E = int(P.h[a ^ u] ^ P.h[a] ^ F.mul[P.d[a ^ u], a & u])
            out.append((ui, u, a, A, mu, y, int(P.h[a]), E))
    return out


def formula_G(P, dtype=np.int64):
    F = P.F
    q = F.q
    nU = len(P.U)
    S = np.repeat(np.arange(q), q - 1)
    X = np.tile(np.arange(1, q), q)
    Z = S & X
    nz = Z != 0
    cols = np.nonzero(nz)[0]
    Sc, Xc, Zc = S[nz], X[nz], Z[nz]
    g = np.zeros((nU * (q - 1), q * (q - 1)), dtype=dtype)
    adj_cache = {}
    for (ui, u, a, A, mu, y, ha, E) in atoms(P):
        if A not in adj_cache:
            adj_cache[A] = F.adjT(A)
        eta = adj_cache[A][Zc]
        C = ha ^ F.mul[mu, Sc ^ E]
        sg = F.par[Xc & y] ^ F.par[Zc & C]
        rows = ui * (q - 1) + eta - 1
        np.add.at(g, (rows, cols), (1 - 2 * sg).astype(dtype))
    return g


def M_mult(P):
    """M(p,d) = max_{y,nu} #{(u,a): u notin {0,rho}, D_u p(a)=y, d(a)/K(u)=nu}."""
    F = P.F
    q = F.q
    cnt = np.zeros(q * q, dtype=np.int64)
    a = np.arange(q)
    for u in P.U:
        kin = int(F.inv[int(P.K[u])])
        y = P.p[a ^ u] ^ P.p
        nu = F.mul[P.d, kin]
        cnt += np.bincount(y * q + nu, minlength=q * q)
    return int(cnt.max()), cnt
