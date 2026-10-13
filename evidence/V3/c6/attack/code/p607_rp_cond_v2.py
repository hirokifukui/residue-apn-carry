"""[v2: v1 crashed because c6 had no saved S-box tables; tables now regenerated and compared to c5 copies]
C6 attack lane P6-07 (Claude 2026-10-11): independent re-implementation of the conditioning bound
    P_RP(A) <= min(1, K N^{-sw} M^Q / (M)_Q),  K = N^{3w}, M = N^w, Q = sN
(does NOT import gpt_input/.../rp_conditioning.py).  Exact Python integers / Fractions; outward comparison by
integer cross-multiplication.  Also: old additive switching bound N^{(3-s)w} + C(Q,2)/M, exact tiny conditioning
check RP == RF|D (all tuples), and structural checks that G_theta is a bijection of R^w for every theta
(the hypothesis used for P_RF(one theta passes s disjoint slices) = N^{-sw}).
usage: python3 -I -B p607_rp_cond.py OUT.json
"""
import sys, os, json, math, itertools, time
sys.dont_write_bytecode = True
from fractions import Fraction


def falling(M, Q):
    r = 1
    for i in range(Q):
        r *= (M - i)
    return r


def log2_frac(f):
    return math.log2(f.numerator) - math.log2(f.denominator)


CASES = [  # (label, N, w, s, claimed strict upper)
    ('m3w2s4', 64, 2, 4, Fraction(9, 10)),
    ('m3w2s5', 64, 2, 5, Fraction(1, 40)),
    ('m5w2s4', 1024, 2, 4, Fraction(1, 300)),
    ('m5w2s5', 1024, 2, 5, Fraction(1, 4000000)),
    ('m5w4s4', 1024, 4, 4, Fraction(2, 1024 ** 4)),
]
EXTRA = [('m3w2s3', 64, 2, 3), ('m3w2s6', 64, 2, 6), ('m5w2s3', 1024, 2, 3), ('m5w2s6', 1024, 2, 6),
         ('m5w4s3', 1024, 4, 3), ('m5w4s5', 1024, 4, 5), ('m3w3s4', 64, 3, 4)]


def bound(N, w, s):
    M = N ** w; Q = s * N; K = N ** (3 * w)
    assert Q <= M and s <= N ** (w - 1)          # s disjoint one-word slices exist, all Q inputs distinct
    PD = Fraction(falling(M, Q), M ** Q)          # P_RF(D) exact
    rf = Fraction(K, N ** (s * w))                # union bound P_RF(A) <= K N^{-sw}
    new = rf / PD
    old = rf + Fraction(Q * (Q - 1), 2 * M)       # C5 additive switching
    return M, Q, K, PD, rf, new, old


def main(outp):
    t0 = time.time(); out = {'cases': [], 'extra': []}
    for lab, N, w, s, up in CASES:
        M, Q, K, PD, rf, new, old = bound(N, w, s)
        lt = new.numerator * up.denominator < up.numerator * new.denominator
        rec = {'label': lab, 'N': N, 'w': w, 's': s, 'M': M, 'Q': Q, 'K=N^3w': K,
               'RF_union': str(rf), 'log2_RF_union': log2_frac(rf),
               'log2_P_RF(D)': log2_frac(PD), 'ln_1/P_RF(D)': -log2_frac(PD) * math.log(2),
               'Q(Q-1)/(2M)': Q * (Q - 1) / (2 * M),
               'new_num_bits': new.numerator.bit_length(), 'new_den_bits': new.denominator.bit_length(),
               'log2_new': log2_frac(new), 'log10_new': log2_frac(new) * math.log10(2),
               'claimed_upper': str(up), 'new_lt_claimed (exact)': bool(lt),
               'new_lt_1': bool(new < 1),
               'old_additive': str(old), 'old_float': float(old), 'old_vacuous': bool(old >= 1),
               'advantage_lower_1-new': 'exact 1-new; >= 1-' + str(up) if lt else None}
        out['cases'].append(rec); print(lab, {k: rec[k] for k in ('log2_new', 'new_lt_claimed (exact)', 'old_float')}, flush=True)
    for lab, N, w, s in EXTRA:
        M, Q, K, PD, rf, new, old = bound(N, w, s)
        out['extra'].append({'label': lab, 'Q': Q, 'log2_RF_union': log2_frac(rf), 'log2_new': log2_frac(new),
                             'new_ge_1(vacuous)': bool(new >= 1), 'old_float': float(old), 'old_vacuous': bool(old >= 1)})
    # ---- C5-06 exponent: expected false theta under RF after s=4 slices = N^{(3-4)w} = N^{-w}
    out['C5-06'] = {'m5w2_s4_expected_false_theta': '1/1024^2 = ' + str(Fraction(1, 1024 ** 2)),
                    'float': 1 / 1024 ** 2, 'old_text_N^-2w': 1 / 1024 ** 4}
    # ---- tiny exact conditioning check: M=5, Q=3; distribution RP == RF | D tuple by tuple
    Mt, Qt = 5, 3
    rf_all = list(itertools.product(range(Mt), repeat=Qt))
    D = [y for y in rf_all if len(set(y)) == Qt]
    # RP on 3 fixed distinct inputs of a uniform permutation of {0..4}: enumerate all 120 permutations
    rp_counts = {}
    for perm in itertools.permutations(range(Mt)):
        y = (perm[0], perm[2], perm[4]); rp_counts[y] = rp_counts.get(y, 0) + 1
    same = all(Fraction(rp_counts.get(y, 0), 120) == Fraction(1, len(D)) for y in D) and set(rp_counts) == set(D)
    A = lambda y: (y[0] + y[1] + y[2]) % Mt == 0
    pRF_A = Fraction(sum(map(A, rf_all)), len(rf_all)); pRP_A = Fraction(sum(c for y, c in rp_counts.items() if A(y)), 120)
    pD = Fraction(len(D), len(rf_all))
    out['tiny'] = {'M': Mt, 'Q': Qt, 'RP_equals_RF_given_D': bool(same), 'P_RF(D)': str(pD),
                   'P_RF(D)==(M)_Q/M^Q': pD == Fraction(falling(Mt, Qt), Mt ** Qt),
                   'P_RF(A)': str(pRF_A), 'P_RP(A)': str(pRP_A), 'bound': str(pRF_A / pD),
                   'holds': bool(pRP_A <= pRF_A / pD)}
    # ---- structural: G_theta bijection of R^w; coefficient test == ring zero
    HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
    import numpy as np
    from atk_common import build_cipher, Public, mds2, DATA, natural_table, save_table
    st = {}
    from atk_common import pd_inverse_table, ringlib, APN
    R3 = ringlib.GR4(3); Tn3 = R3.encode(R3.horner({1, 3, 9}, R3.all)).astype(np.int64)
    C5D = os.path.join(APN, 'c5', 'attack', 'results', 'data')
    tabs = [('pd_m3_inv_h0', 3, save_table('F_pd_m3_inv_h0', pd_inverse_table(3, 'h0'))),
            ('pd_m3_inv_a3', 3, save_table('F_pd_m3_inv_a3', pd_inverse_table(3, 'a3'))),
            ('nat_m3', 3, save_table('F_nat_m3_X1_X3_X9', Tn3))]
    for nm, _, p in tabs:   # same tables as C5 (read-only comparison)
        assert np.array_equal(np.load(p), np.load(os.path.join(C5D, os.path.basename(p)))), nm
    T5, _ = natural_table(5, 3); tabs.append(('nat_m5_P53', 5, save_table('F_nat_m5_P53', T5)))
    for name, m, p in tabs:
        c = build_cipher(m, 2, p, mds2()); pub = Public(c); rg, sb = c.rg, c.sb; N = pub.N
        codes = np.arange(N, dtype=np.int64)
        S1inv_bij = all(len(set(sb.Binv(rg.sub(sb.Finv(codes), np.full(N, k, np.int64))).tolist())) == N
                        for k in range(N))
        # M3inv * M3 = I via action on unit vectors
        M3 = [[int(v) for v in row] for row in c.M3] if hasattr(c, 'M3') else mds2()
        e = [[np.array([1 if i == j else 0]) for i in range(2)] for j in range(2)]
        ok_inv = all([int(v[0]) for v in rg.mat_apply(pub.M3inv, rg.mat_apply(M3, e[j]))] == [1 if i == j else 0 for i in range(2)]
                     for j in range(2))
        # ring addition == coefficientwise mod 4 in the (bit i, bit m+i) encoding used by the accept test
        a = np.repeat(codes, N); b = np.tile(codes, N); s_ = rg.add(a, b)
        coef = lambda v, i: ((v >> i) & 1) + 2 * ((v >> (m + i)) & 1)
        add_ok = all(np.array_equal(coef(s_, i), (coef(a, i) + coef(b, i)) % 4) for i in range(m))
        st[name] = {'N': N, 'S1inv(.;k)_bijective_all_k': bool(S1inv_bij), 'M3inv_M3_eq_I': bool(ok_inv),
                    'M3_source': 'c.M3' if hasattr(c, 'M3') else 'mds2()',
                    'ring_add_eq_coefwise_mod4_all_pairs': bool(add_ok)}
        print(name, st[name], flush=True)
    out['structural'] = st
    out['seconds'] = round(time.time() - t0, 2)
    ok = all(r['new_lt_claimed (exact)'] for r in out['cases']) and out['tiny']['holds'] and out['tiny']['RP_equals_RF_given_D'] \
        and all(all(v for k, v in d.items() if isinstance(v, bool)) for d in st.values())
    out['P607'] = 'PASS' if ok else 'FAIL'
    json.dump(out, open(outp, 'w'), indent=1, default=str); print('P607=' + out['P607'], out['seconds'])
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
