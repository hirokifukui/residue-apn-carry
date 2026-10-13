"""P5-04 calibration of Theorem UE (independent arithmetic, a1c5_lib only; reads base tables as DATA only).

For each PD table F (B = J o F):
  * PD hypotheses (H) re-checked from the table (APN permutation p, d F2-affine, zero-free, ker K = {0,rho}).
  * Per G direction u (u not in {0,rho}), all terms computed independently of the DDT:
      A_u     = sum_a 2^{wt(w(a) u)}                          (structure: lambda, w)
      Cross_u = sum_{(a,a') different columns} 3^{m - wt(D_u p(a) xor D_u p(a'))}
      Merge_u = #{(s,a,a') : a' in {a^rho, a^rho^u}, same output cell}   -- from DIRECT cipher evaluation
                (row v=0; v-independence re-checked at two more v)
    and checked: r_a != 0, per (a,partner) #s <= q/2, Merge_u <= q^2, A_u <= 4(3^m-1),
    Cross_u <= 2q(q^2-3^m), Cross_u == sum_s 2^{m-wt s} Pairs_u(s) (C4 form).
  * Row energies E(alpha) = sum_delta C(alpha,delta)^2 from the actual cipher (m5: full integer DDT;
    m7: per-row counting, no table stored) -> identity sum_v E(u,v) = q^3 + q A_u + Cross_u + q Merge_u,
    Z sum exact = 2(3/4)^m - 2/q, E rows max count <= q and energy <= 1, total <= 6 + 4(3/4)^m.
usage: python3 -I -B a1c5_ue.py 5|7
"""
import sys, os, json, time, hashlib
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from a1c5_lib import GF, ring_ops, build_lifts, extract_pd, ddt

BASE = os.path.expanduser('~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher')


def cipher_rows_v(K, B, u, v):
    """T[s, a] = output hi-difference for input difference (u,v), output lo-difference s, point a."""
    m, q = K.m, K.q; add, neg, sub, J = ring_ops(m)
    N = q * q; X = np.arange(N)
    D = sub(B[add(X, u | (v << m))], B)
    s = D & (q - 1); t = D >> m; a = X & (q - 1)
    T = -np.ones((q, q), dtype=np.int64)
    T[s, a] = t
    # uniqueness: each (a,s) hit exactly once
    cnt = np.zeros((q, q), dtype=np.int64); np.add.at(cnt, (s, a), 1)
    assert np.all(cnt == 1), 'b not unique for (a,s)'
    return T


def per_u(K, pd, B, u, row_energy):
    m, q = K.m, K.q; A = np.arange(q); rho = pd['rho']; d = pd['d']; Kl = pd['K']; p = pd['p']
    Ku = int(Kl[u]); Kinv = int(K.INV[Ku])
    lam = K.MUL[d, Kinv]
    w = K.MUL[K.MUL[lam, lam[A ^ u]], Ku]
    assert np.array_equal(lam[A ^ u], lam ^ 1)
    # columns = level sets of w
    col = np.minimum.reduce([A, A ^ u, A ^ rho, A ^ u ^ rho])
    for a in range(q):
        assert set(np.nonzero(w == w[a])[0].tolist()) == {a, a ^ u, a ^ rho, a ^ u ^ rho}
    wu = K.MUL[w, u]; assert np.all(wu != 0)
    A_u = int(np.sum(2 ** K.wt[wu]))
    dp = p[A ^ u] ^ p
    R = dp[:, None] ^ dp[None, :]
    diff = col[:, None] != col[None, :]
    assert np.all(R[diff] != 0)
    cross = int(np.sum(3 ** (m - K.wt[R[diff]])))
    # C4 form: sum_s 2^{m-wt s} Pairs_u(s)
    c4 = 0
    for s in range(q):
        c4 += (1 << (m - int(K.wt[s]))) * int(np.sum(((R & ~s & (q - 1)) == 0) & diff))
    assert c4 == cross
    # merge from direct evaluation
    T0 = cipher_rows_v(K, B, u, 0)
    merge = 0; maxper = 0; ra_zero = 0
    for off in (rho, rho ^ u):
        eq = (T0 == T0[:, A ^ off])                 # [s, a]
        per = eq.sum(axis=0); maxper = max(maxper, int(per.max()))
        merge += int(per.sum())
        ra_zero += int(np.sum(dp == dp[A ^ off]))
    assert ra_zero == 0, 'r_a = 0 somewhere'
    vchk = []
    for v in (1, q - 1):
        Tv = cipher_rows_v(K, B, u, v)
        mv = sum(int(np.sum(Tv == Tv[:, A ^ off])) for off in (rho, rho ^ u))
        vchk.append(mv)
    assert all(x == merge for x in vchk), ('merge depends on v', merge, vchk)
    ok = (maxper <= q // 2 and merge <= q * q and A_u <= 4 * (3 ** m - 1) and cross <= 2 * q * (q * q - 3 ** m))
    assert ok, (u, maxper, merge, A_u, cross)
    rec = {'A_u': A_u, 'Cross_u': cross, 'Merge_u': merge, 'max_s_per_pair': maxper,
           'C4_merge_bound': q * q + A_u}
    if row_energy is not None:
        E = row_energy(u)
        rec['sumE'] = E
        assert E == q ** 3 + q * A_u + cross + q * merge, ('identity', u, E)
    return rec


def make_row_energy_fn(K, B, C):
    m, q = K.m, K.q; add, neg, sub, J = ring_ops(m); N = q * q; X = np.arange(N)
    if C is not None:
        def rowE(al): return int(np.sum(C[al] * C[al]))
        def rowMax(al): return int(C[al].max())
    else:
        def _cnt(al):
            _, c = np.unique(sub(B[add(X, al)], B), return_counts=True); return c.astype(np.int64)
        def rowE(al): c = _cnt(al); return int(np.sum(c * c))
        def rowMax(al): return int(_cnt(al).max())
    def uE(u): return sum(rowE(u | (v << m)) for v in range(q))
    return rowE, rowMax, uE


def main():
    m = int(sys.argv[1]); K = GF(m); q = K.q; N = q * q
    which = ('natural', 'h0', 'random', 'inv', 'rho')
    lifts, Fn = build_lifts(K, which)
    base = np.load(BASE + '/c1/data/F_m%d_r3.npy' % m).astype(np.int64)
    out = {'m': m, 'natural_equals_c1_base_table': bool(np.array_equal(Fn, base)), 'lifts': {}}
    if m == 5:     # adversarial lifts of C3/C4 as data
        for nm, f in (('c1_adversarialG', BASE + '/c1/data/F_m5_r3_adversarialG.npy'),
                      ('c3_Gpair', BASE + '/c3/a1/data/F_Gpair.npy'), ('c3_Gconc', BASE + '/c3/a1/data/F_Gconc.npy')):
            lifts[nm] = np.load(f).astype(np.int64)
    add, neg, sub, J = ring_ops(m)
    for name, F in lifts.items():
        t0 = time.time()
        pd = extract_pd(K, F); rho = pd['rho']
        B = J(F)
        C = ddt(m, B) if m == 5 else None
        rowE, rowMax, uE = make_row_energy_fn(K, B, C)
        Gu = [u for u in range(1, q) if u != rho]
        recs = {u: per_u(K, pd, B, u, uE) for u in Gu}
        G_tot = sum(r['sumE'] for r in recs.values())
        Z_tot = sum(rowE(v << m) for v in range(1, q))
        E_rows = [rho | (v << m) for v in range(q)]
        E_max = max(rowMax(al) for al in E_rows)
        E_tot = sum(rowE(al) for al in E_rows)
        zero = rowE(0)
        assert zero == N * N
        assert E_max <= q
        Zf = Fraction(Z_tot, N * N); Zexact = 2 * Fraction(3, 4) ** m - Fraction(2, q)
        assert Zf == Zexact, (Zf, Zexact)
        Gf = Fraction(G_tot, N * N); Ef = Fraction(E_tot, N * N)
        tot = 1 + Zf + Ef + Gf
        Gbound = Fraction((q - 2) * (4 * q ** 3 + 2 * q * 3 ** m - 4 * q), N * N)
        UE = 6 + 4 * Fraction(3, 4) ** m
        assert Ef <= 1 and Gf <= Gbound and tot <= UE
        rec = {'rho': int(rho), 'wt_rho': bin(rho).count('1'), 'F_sha256': hashlib.sha256(F.astype('<i8').tobytes()).hexdigest(),
               'max_Merge_u': max(r['Merge_u'] for r in recs.values()), 'q2': q * q,
               'max_C4_merge_bound': max(r['C4_merge_bound'] for r in recs.values()),
               'max_s_per_pair': max(r['max_s_per_pair'] for r in recs.values()), 'q_half': q // 2,
               'max_A_u': max(r['A_u'] for r in recs.values()), 'A_bound': 4 * (3 ** m - 1),
               'max_Cross_u': max(r['Cross_u'] for r in recs.values()), 'Cross_bound': 2 * q * (q * q - 3 ** m),
               'max_sumE_u': max(r['sumE'] for r in recs.values()), 'sumE_bound': 4 * q ** 3 + 2 * q * 3 ** m - 4 * q,
               'E_rows_max_count': E_max,
               'calE_zero': 1, 'calE_Z': str(Zf), 'calE_Z_exact_formula': str(Zexact),
               'calE_E': str(Ef), 'calE_E_float': float(Ef),
               'calE_G': str(Gf), 'calE_G_float': float(Gf), 'calE_G_bound': str(Gbound), 'calE_G_bound_float': float(Gbound),
               'calE_B': str(tot), 'calE_B_float': float(tot), 'UE_bound': str(UE), 'UE_bound_float': float(UE),
               'identity_checked_all_G_u': True, 'n_G_dirs': len(Gu), 'sec': round(time.time() - t0, 1)}
        out['lifts'][name] = rec
        print(name, json.dumps({k: v for k, v in rec.items() if k != 'F_sha256'}), flush=True)
    json.dump(out, open(BASE + '/c5/a1/results/a1c5_ue_m%d.json' % m, 'w'), indent=1)
    print('A1C5_UE_M%d=PASS' % m)


if __name__ == '__main__':
    main()
