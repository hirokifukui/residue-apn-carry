#!/usr/bin/env python3
"""P5-07 / P5-08 (C5, Claude PD lane, 2026-10-11).  Independent arithmetic (own GF(2^m) carry-less multiply, own Z4^m
coefficientwise ring add/sub); c1/c2/c3/c4/gpt_input are only READ (tables loaded for comparison), never modified.

F(a,b) = (p(a), h(a) xor d(a) b) on codes x = a | (b << m)  (lo digit a, hi digit b; ring element sum (a_i + 2 b_i) t^i).
PD tables (m = 5, field t^5+t^2+1):  p = x^{-1} (0 -> 0),  d0 = a^4 + a^2 + 1,  h in {0, a, a^3}.
Reference tables (read only):  natural F = c1/data/F_m5_r3.npy,  PD h0 = c4/pd/data/F_pd_inv_m5.npy,
                               PD h_C3 = c4/pd/data/F_pd_inv_hC3_m5.npy,  auditor hX3 = gpt_input/.../auditor_PD_inverse_hX3_m5.npy.

Psi_{kappa,mu}(c) = XOR_a p( h(a) xor d(a)(c xor (a & kappa)) xor mu ),   kappa, mu, c in F_q   (C4 lemma Psi).
Per table: number of (kappa,mu) with Psi == 0 (all c), split into
   PAIR  : e_h(a) := (h(a^rho) ^ h(a)) / d(a) is constant == kappa & rho   (pointwise pair coincidence)
   AFF0  : kappa = 0 and h, d F2-affine (proposition B1)
   OTHER : Psi == 0 explained by neither.
Direct cross-check: lo s(a) = XOR_b lo S2(a,b) on the isolated S2 block (c2 Macro.S via c4 SplitTail ftable, read only)
for all K1 in R (1024) x 32 K2 (lo K2 = mu runs over F_q, hi K2 = fixed): count of lo s == 0 must equal 32 x #zero pairs
... and the identity of which (kappa,mu) are zero.
PD hypotheses (theorem PD): p permutation, DU(p) = 2, d affine, ker K = {0,rho}, eps = d(0) not in Im K, d nowhere zero.
Exact EDP_t (t=1..3) = max_{alpha != 0} (CB^t CF)[alpha, :] / N^(t+1), integer int64, ring differences
   C_G[alpha, beta] = #{x : G(x + alpha) - G(x) = beta}.  B = J o F (J swaps digits).
usage: python3 -I -B pd5_math.py OUT.json
"""
import os, sys, json, time, hashlib
sys.dont_write_bytecode = True
import numpy as np
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
APN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
DATA = os.path.join(APN, 'c5', 'pd', 'data')
AUD = os.path.join(APN, 'gpt_input', 'extracted_P5', 'ResidueAPN_P4_C4_Reviewed_P5_20261011', 'evidence')


# ---------------- own arithmetic ----------------
def gf_mul_table(m, mod):
    q = 1 << m; T = np.zeros((q, q), np.int64)
    for x in range(q):
        for y in range(q):
            r = 0
            for i in range(m):
                if (y >> i) & 1: r ^= x << i
            for k in range(2 * m - 2, m - 1, -1):
                if (r >> k) & 1: r ^= mod << (k - m)
            T[x, y] = r
    return T


def gf_pow(x, e, MUL):
    r = 1
    for _ in range(e): r = int(MUL[r, x])
    return r


def radd(x, y, m):
    mk = (1 << m) - 1; a, c = x & mk, y & mk
    return (a ^ c) | ((((x >> m) ^ (y >> m) ^ (a & c)) & mk) << m)


def rneg(x, m):
    mk = (1 << m) - 1; a = x & mk
    return a | ((((x >> m) ^ a) & mk) << m)


def rsub(x, y, m):
    return radd(x, rneg(y, m), m)


def build(p, h, d, MUL, m):
    q = 1 << m; X = np.arange(q * q, dtype=np.int64); A = X & (q - 1); Bv = X >> m
    return (p[A] | ((h[A] ^ MUL[d[A], Bv]) << m)).astype(np.int64)


def decompose(F, MUL, m):
    q = 1 << m; a = np.arange(q)
    p = F[a] & (q - 1); h = F[a] >> m; d = (F[a | (1 << m)] >> m) ^ h
    ok = np.array_equal(build(p, h, d, MUL, m), F)
    return p, h, d, ok


def sha_arr(T):
    return hashlib.sha256(np.ascontiguousarray(np.asarray(T).astype(np.int64)).tobytes()).hexdigest()


def sha_file(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def anf_deg(v):
    a = np.asarray(v, np.int64).copy(); n = len(a); s = 1
    while s < n:
        idx = np.arange(n); sel = (idx & s) != 0; a[sel] ^= a[idx[sel] ^ s]; s <<= 1
    nz = np.nonzero(a)[0]
    return int(max(bin(int(i)).count('1') for i in nz)) if nz.size else -1


def is_affine(v, m):
    return anf_deg(v) <= 1


# ---------------- Psi ----------------
def psi_zero_matrix(p, h, d, MUL, m):
    """Z[kappa, mu] = True iff Psi_{kappa,mu}(c) = 0 for every c."""
    q = 1 << m; a = np.arange(q); c = np.arange(q)[:, None]; Z = np.zeros((q, q), bool)
    for kap in range(q):
        arg = h[None, :] ^ MUL[d[None, :], c ^ (a & kap)[None, :]]          # (c, a)
        for mu in range(q):
            Z[kap, mu] = not np.any(np.bitwise_xor.reduce(p[arg ^ mu], axis=1))
    return Z


def e_h(h, d, MUL, m, rho):
    q = 1 << m; a = np.arange(q)
    dinv = np.array([gf_pow(int(x), q - 2, MUL) for x in d], np.int64)
    return MUL[h[a ^ rho] ^ h, dinv]


def classify(p, h, d, MUL, m):
    q = 1 << m; eps = int(d[0]); K = d ^ eps
    ker = [u for u in range(q) if K[u] == 0]; rho = ker[1] if len(ker) == 2 else None
    Z = psi_zero_matrix(p, h, d, MUL, m)
    e = e_h(h, d, MUL, m, rho); econst = bool(np.all(e == e[0]))
    pair_k = [k for k in range(q) if econst and int(e[0]) == (k & rho)]
    aff = is_affine(h, m) and is_affine(d, m)
    pair = np.zeros((q, q), bool); pair[pair_k, :] = True
    aff0 = np.zeros((q, q), bool)
    if aff: aff0[0, :] = True
    other = Z & ~pair & ~aff0
    return {'rho': rho, 'e_h_constant': econst, 'e_h_distinct_values': int(len(np.unique(e))),
            'e_h_value_if_const': int(e[0]) if econst else None,
            'h_affine': is_affine(h, m), 'd_affine': is_affine(d, m), 'h_anf_degree': anf_deg(h),
            'psi_zero_pairs': int(Z.sum()), 'total_pairs': q * q,
            'pair_class_pairs': int(pair.sum()), 'pair_class_kappa_fraction': str(Fr(len(pair_k), q)),
            'aff0_class_pairs': int(aff0.sum()), 'aff0_kappa_fraction': str(Fr(1, q)) if aff else '0',
            'pair_and_aff0_overlap': int((pair & aff0).sum()),
            'pair_implies_zero': bool(np.all(Z[pair])), 'aff0_implies_zero': bool(np.all(Z[aff0])),
            'other_zero_pairs': int(other.sum()),
            'zero_kappas': sorted(set(int(k) for k in np.nonzero(Z)[0])),
            'zero_by_kappa_count': {int(k): int(Z[k].sum()) for k in range(q) if Z[k].any()}}, Z


# ---------------- PD hypotheses / DDT ----------------
def pd_hyp(p, d, MUL, m):
    q = 1 << m; a = np.arange(q); eps = int(d[0]); K = d ^ eps
    du = 0
    for u in range(1, q): du = max(du, int(np.bincount(p[a ^ u] ^ p, minlength=q).max()))
    ImK = set(int(v) for v in K)
    ker = [u for u in range(q) if K[u] == 0]
    return {'p_perm': len(set(p.tolist())) == q, 'DU_p': du, 'p_anf_degree': anf_deg(p), 'd_affine': is_affine(d, m),
            'kerK': ker, 'eps': eps, 'eps_not_in_ImK': eps not in ImK, 'ImK_size': len(ImK),
            'd_nowhere_zero': bool(np.all(d != 0)),
            'PD_holds': bool(len(set(p.tolist())) == q and du == 2 and is_affine(d, m) and len(ker) == 2
                             and eps not in ImK and np.all(d != 0))}


def ddt(G, m):
    N = len(G); X = np.arange(N, dtype=np.int64); C = np.empty((N, N), np.int64)
    for al in range(N):
        C[al] = np.bincount(rsub(G[radd(X, al, m)], G, m), minlength=N)
    assert np.all(C.sum(1) == N) and np.all(C.sum(0) == N)
    return C


def edp(F, m, tmax=3):
    N = len(F); q = 1 << m
    Bt = ((F & (q - 1)) << m) | (F >> m)                    # J o F
    CF = ddt(F, m); CB = ddt(Bt, m)
    out = {'DU_F': int(CF[1:].max()), 'DU_B': int(CB[1:].max())}
    cur = CF.copy()
    for t in range(1, tmax + 1):
        cur = CB @ cur
        assert int(cur.max()) < 2 ** 62
        mx = int(cur[1:].max()); out[f'NxEDP{t}'] = str(Fr(mx * N, N ** (t + 1))); out[f'raw_max_t{t}'] = mx
    out['NxEDP2_le_4'] = Fr(out['NxEDP2']) <= 4
    return out


def lo_s_direct(Fpath, Z, m=5):
    """direct S2 computation via c4 SplitTail(ftable) -> c2 Macro.S (read-only import)."""
    sys.path.insert(0, os.path.join(APN, 'c4', 'macro'))
    from macro_p4 import SplitTail, mixers
    q = 1 << m; N = q * q; X = np.arange(N, dtype=np.int64); A = X & (q - 1)
    c = SplitTail(5, 2, mixers(5)['MDS_alt'], ftable=Fpath)
    hiK2 = 17; agree = 0; nz = 0; tot = 0
    for K1 in range(N):
        for mu in range(q):
            Y = c.base.S(X, [K1, mu | (hiK2 << m)])
            los = np.zeros(q, np.int64); np.bitwise_xor.at(los, A, Y & (q - 1))
            z = not np.any(los); nz += z; tot += 1; agree += (z == bool(Z[K1 & (q - 1), mu]))
    return {'keys': tot, 'lo_s_zero_keys': int(nz), 'expected_32x_zero_pairs': int(32 * Z.sum()),
            'per_key_agreement_with_Psi': agree == tot, 'sbox_sha256': c.sb.F_sha256}


def main(outp):
    t0 = time.time(); m = 5; q = 32; N = 1024
    MUL = gf_mul_table(m, 0b100101)
    a = np.arange(q)
    inv = np.array([0] + [gf_pow(x, q - 2, MUL) for x in range(1, q)], np.int64)
    assert all(MUL[x, inv[x]] == 1 for x in range(1, q))
    d0 = np.array([gf_pow(x, 4, MUL) ^ gf_pow(x, 2, MUL) ^ 1 for x in range(q)], np.int64)
    a3 = np.array([gf_pow(x, 3, MUL) for x in range(q)], np.int64)
    # d0 = (a^2+a+1)^2  and  e_h for h=a^3 is 1/(a^2+a+1)  (paper claims, checked)
    s = np.array([gf_pow(x, 2, MUL) ^ x ^ 1 for x in range(q)], np.int64)
    res = {'id': 'P5-07/P5-08 independent math (m5)', 'field': 't^5+t^2+1 (0b100101)',
           'd0_eq_(a^2+a+1)^2': bool(np.array_equal(d0, MUL[s, s]))}
    tabs = {'PD_h0': build(inv, np.zeros(q, np.int64), d0, MUL, m),
            'PD_hA': build(inv, a.astype(np.int64), d0, MUL, m),
            'PD_hX3': build(inv, a3, d0, MUL, m)}
    # ring-arith self check vs c1 (read only)
    sys.path.insert(0, os.path.join(APN, 'c1', 'code'))
    from codes import mk
    add1, neg1, sub1, J1 = mk(m); rng = np.random.default_rng(5070); xx = rng.integers(0, N, 50000); yy = rng.integers(0, N, 50000)
    res['own_ring_add_sub_eq_c1'] = bool(np.array_equal(radd(xx, yy, m), add1(xx, yy)) and np.array_equal(rsub(xx, yy, m), sub1(xx, yy)))
    # save my tables
    files = {}
    for nm, T in tabs.items():
        assert len(np.unique(T)) == N
        pth = os.path.join(DATA, f'F_{nm}_m5.npy'); np.save(pth, T)
        files[nm] = {'path': os.path.relpath(pth, APN), 'file_sha256': sha_file(pth), 'array_int64_sha256': sha_arr(T)}
    res['my_tables'] = files
    ref = {'natural_F': os.path.join(APN, 'c1', 'data', 'F_m5_r3.npy'),
           'C4_PD_h0': os.path.join(APN, 'c4', 'pd', 'data', 'F_pd_inv_m5.npy'),
           'C4_PD_hC3': os.path.join(APN, 'c4', 'pd', 'data', 'F_pd_inv_hC3_m5.npy'),
           'AUD_PD_hX3': os.path.join(AUD, 'auditor_PD_inverse_hX3_m5.npy'),
           'AUD_PD_hX': os.path.join(AUD, 'auditor_PD_inverse_hX_m5.npy')}
    R = {k: np.load(v).astype(np.int64) for k, v in ref.items()}
    res['reference_tables'] = {k: {'file_sha256': sha_file(v), 'array_int64_sha256': sha_arr(R[k])} for k, v in ref.items()}
    res['cmp'] = {'my_h0_eq_C4_h0': bool(np.array_equal(tabs['PD_h0'], R['C4_PD_h0'])),
                  'my_hX3_eq_auditor_hX3': bool(np.array_equal(tabs['PD_hX3'], R['AUD_PD_hX3'])),
                  'my_hA_eq_auditor_hX': bool(np.array_equal(tabs['PD_hA'], R['AUD_PD_hX']))}
    allT = {'natural_F': R['natural_F'], 'PD_h0': tabs['PD_h0'], 'PD_hA': tabs['PD_hA'],
            'PD_hC3': R['C4_PD_hC3'], 'PD_hX3': tabs['PD_hX3']}
    paths = {'natural_F': ref['natural_F'], 'PD_h0': os.path.join(DATA, 'F_PD_h0_m5.npy'),
             'PD_hA': os.path.join(DATA, 'F_PD_hA_m5.npy'), 'PD_hC3': ref['C4_PD_hC3'],
             'PD_hX3': os.path.join(DATA, 'F_PD_hX3_m5.npy')}
    res['tables'] = {}
    for nm, T in allT.items():
        p, h, d, ok = decompose(T, MUL, m)
        rec = {'form_ok': ok, 'array_int64_sha256': sha_arr(T), 'hyp': pd_hyp(p, d, MUL, m)}
        cl, Z = classify(p, h, d, MUL, m); rec['psi'] = cl
        print(nm, 'psi', cl['psi_zero_pairs'], 'pair', cl['pair_class_pairs'], 'aff0', cl['aff0_class_pairs'],
              'other', cl['other_zero_pairs'], round(time.time() - t0, 1), flush=True)
        rec['direct_lo_s'] = lo_s_direct(paths[nm], Z)
        print(nm, 'direct', rec['direct_lo_s'], round(time.time() - t0, 1), flush=True)
        rec['edp'] = edp(T, m)
        print(nm, 'edp', rec['edp'], round(time.time() - t0, 1), flush=True)
        res['tables'][nm] = rec
        json.dump(res, open(outp, 'w'), indent=1, default=str)
    # h = a^e scan (search for a third cancellation mechanism), p = inv, d = d0
    scan = {}
    for e in range(0, 31):
        he = np.array([gf_pow(x, e, MUL) if (x or e) else (1 if e == 0 else 0) for x in range(q)], np.int64)
        if e == 0: he = np.ones(q, np.int64)
        cl, Z = classify(inv, he, d0, MUL, m)
        scan[e] = {k: cl[k] for k in ('psi_zero_pairs', 'pair_class_pairs', 'aff0_class_pairs', 'other_zero_pairs',
                                       'e_h_constant', 'h_anf_degree', 'zero_kappas')}
    res['scan_h_eq_a^e_(e=0 is h=1)'] = scan
    res['time_s'] = round(time.time() - t0, 1)
    json.dump(res, open(outp, 'w'), indent=1, default=str)
    print('DONE', res['time_s'], json.dumps(res['cmp']), flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
