#!/usr/bin/env python3
"""p312_pd_roles.py -- P3-12 (C3, Claude 2026-10-10).  m = 5 only.  New file; c1/, c2/ are read only.

Part 1  h = 0 lift as a ring polynomial (explicit witness).
   F0 = sigma-lift of P_{5,3} (= C1 natural table F_m5_r3.npy).  h(a) = high digit of F0(sigma(a)).
   H in F_32[X] (deg < 32) interpolates h (Lagrange: c_k = sum_a h(a) a^(31-k), k >= 1; c_0 = h(0)).
   F1 = F0 + 2*Hhat for several coefficient lifts Hhat of H (sigma-lift; sigma-lift + random digit-1 parts;
   a non-reduced representative H + (X^32 - X) G).  Evaluated by Horner over all 1024 points of GR(4,5) with
   ring arithmetic only; compared with the h=0 table (p(a), d(a) b), d = p' (field-side, independent of C1 code)
   and with the C1 oracle-based table used in c2/cost (P53_h0).
Part 2  realizability of an arbitrary pair (p, d): Fbar = prep + (X^q - X)(d + prep') has residue function p and
   formal derivative d on F_q (char 2).  Witness: p = x^(-1) = X^30 (APN permutation, NOT quadratic), d = d0.
Part 3  hypothesis check (p perm, p APN, d affine, ker K = {0, rho}, d non-vanishing) + full-point comparison
   for each map of the form (p(a), h(a) xor d(a) b):
     form check over all 1024 points; Lemma 0 bounds for C_F; eps(B) = 1/q (DU of B = q);
     ClassTransition section 4 column-sum / max-element table; final-layer bounds;
     exact EDP_t (t = 1..4, model A_t = T_B^t T_F) vs the warm-start S recursion (z1 = e1 = 1/q) and
     the uniform constants 4/N (omega = 2) and (6 + 6/q)/N (any omega).
   Maps: natural F, H_A, H_B (c2/cost tables), P1theta sigma-lift and factored lift (own residue p_theta,
   compared with ITS OWN formal derivative), h=0 lift (Part 1 witness), X^30 synthetic (Part 2 witness, random h),
   main p with d(a) = d0(c a) (rho = t, weight 1; rho of weight 3), random h.  Negative control: Dickson g5
   (residue not APN; hypothesis fails, no claim).
usage: python3 -I p312_pd_roles.py OUTDIR
"""
import sys, os, json, time, hashlib
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
C1 = os.path.join(ROOT, 'c1'); C2 = os.path.join(ROOT, 'c2')
sys.path.insert(0, os.path.join(C1, 'code'))
from codes import mk
from ringlib import GR4, GF2m, P_exponents
from ddt import ddt

m, q, N = 5, 32, 1024
MASK = q - 1
add, neg, sub, J = mk(m)
R = GR4(m); K = GF2m(m); MUL = K.MUL
IDX = np.arange(N, dtype=np.int64); LO, HI = IDX & MASK, IDX >> m
rng = np.random.default_rng(20261010)

def popc(x): return bin(int(x)).count('1')
def fpow(a, e): return K.pow(int(a), e) if e > 0 else 1          # 0^0 = 1
def finv(a): return K.pow(int(a), q - 2)
def peval(A, a):
    s = 0
    for e, c in A.items(): s ^= int(MUL[c, fpow(a, e)])
    return s
def padd(A, B):
    C = dict(A)
    for e, c in B.items(): C[e] = C.get(e, 0) ^ c
    return {e: c for e, c in C.items() if c}
def pmul(A, B):
    C = {}
    for e1, c1 in A.items():
        for e2, c2 in B.items(): C[e1 + e2] = C.get(e1 + e2, 0) ^ int(MUL[c1, c2])
    return {e: c for e, c in C.items() if c}
def pder(A): return {e - 1: c for e, c in A.items() if e % 2 == 1}
def interp(vals):
    """deg < q polynomial over F_q with values vals[a]."""
    co = {0: int(vals[0])}
    for k in range(1, q):
        s = 0
        for a in range(q): s ^= int(MUL[int(vals[a]), fpow(a, q - 1 - k)])
        co[k] = s
    co = {e: c for e, c in co.items() if c}
    assert all(peval(co, a) == int(vals[a]) for a in range(q))
    return co

def ring_poly(coeffs):
    """coeffs: exponent -> ring element CODE (low m bits digit 0, high m bits digit 1). Horner, ring ops only."""
    deg = max(coeffs); X = R.all; acc = np.zeros_like(X)
    for e in range(deg, -1, -1):
        acc = R.mul(acc, X)
        if e in coeffs: acc = (acc + R.decode(np.array([coeffs[e]]))[0]) % 4
    return R.encode(acc)

# ---------------------------------------------------------------- Part 1
def part1():
    pexp = sorted(P_exponents(m, 3)); p = {e: 1 for e in pexp}
    F0 = np.load(os.path.join(C1, 'data', 'F_m5_r3.npy')).astype(np.int64)
    F0coef = {e: 1 for e in pexp}
    assert np.array_equal(ring_poly(F0coef), F0)
    h = F0[:q] >> m                                                   # high digit of F0(sigma(a)), b = 0
    H = interp(h)
    ptab = np.array([peval(p, a) for a in range(q)]); dp = pder(p)
    dtab = np.array([peval(dp, a) for a in range(q)])
    target = ptab[LO] | (MUL[dtab[LO], HI] << m)                      # (p(a), d(a) b), field side
    o = json.load(open(os.path.join(C1, 'data', 't303_oracle.json')))[0]
    target_c1 = np.array(o['p_table'])[LO] | (MUL[np.array(o['d_table'])[LO], HI] << m)
    res = {'p_exponents': pexp, 'p_prime_exponents': sorted(dp), 'H_nonzero_terms': len(H), 'H_degree': max(H),
           'H_exponents': sorted(H), 'target_eq_c1_oracle_h0_table': bool(np.array_equal(target, target_c1)),
           'natural_F0_eq_C1_table': True, 'lifts': {}}
    lifts = {'sigma': {e: c for e, c in H.items()}}
    lifts['sigma_plus_random_digit1'] = {e: c | (int(rng.integers(0, q)) << m) for e, c in H.items()}
    G = {e: int(rng.integers(1, q)) for e in (0, 3, 7)}
    Hnr = padd(H, pmul({q: 1, 1: 1}, G)); assert all(peval(Hnr, a) == int(h[a]) for a in range(q))
    lifts['nonreduced_H_plus_(X^32-X)G'] = Hnr
    for name, Hh in lifts.items():
        # build the ring polynomial F0 + 2*Hhat literally (coefficient add in R, digit-1 parts of Hhat are killed by 2)
        coef2 = dict(F0coef)
        for e, c in Hh.items():
            cv = R.decode(np.array([c]))[0]; twoc = R.encode((2 * cv) % 4)
            coef2[e] = int(R.encode((R.decode(np.array([coef2.get(e, 0)]))[0] + 2 * cv) % 4)) if e in coef2 else int(twoc)
        tab = ring_poly(coef2)
        res['lifts'][name] = {'n_terms': len(coef2), 'degree': max(coef2),
                              'eq_h0_table_all_1024': bool(np.array_equal(tab, target)),
                              'sha256': hashlib.sha256(tab.astype(np.int64).tobytes()).hexdigest()[:16]}
        assert np.array_equal(tab, target), name
    print('PART1', json.dumps(res), flush=True)
    return res, target, ptab, dtab, p

# ---------------------------------------------------------------- Part 2
def part2():
    prep = {30: 1}                                                     # x^(-1) on F_32 (0 -> 0)
    d0 = {4: 1, 2: 1, 0: 1}
    G = padd(d0, pder(prep))
    Fbar = padd(prep, pmul({q: 1, 1: 1}, G))
    ok_vals = all(peval(Fbar, a) == peval(prep, a) for a in range(q))
    der = pder(Fbar); der_vals_eq_d0 = all(peval(der, a) == peval(d0, a) for a in range(q))
    # Z4 lift: sigma(prep) + (X^q - X) sigma(G)   (all F_q coefficients are 0/1 here)
    assert all(c == 1 for c in prep.values()) and all(c == 1 for c in G.values())
    Z = {e: 1 for e in prep}
    for e in G:
        Z[e + q] = (Z.get(e + q, 0) + 1) % 4; Z[e + 1] = (Z.get(e + 1, 0) - 1) % 4
    coef = {e: int((c & 1) | ((c >> 1) << m)) for e, c in Z.items() if c % 4}
    tab = ring_poly(coef)
    res = {'p': 'X^30 (= x^-1, x^-1(0)=0)', 'd': 'd0 = X^4+X^2+1', 'Fbar_exponents': sorted(Fbar),
           'Fbar_values_eq_p': ok_vals, 'formal_derivative_values_eq_d0': der_vals_eq_d0,
           'Z4_coeffs': {str(e): c for e, c in sorted(Z.items()) if c % 4}}
    print('PART2', json.dumps(res), flush=True)
    return res, tab

# ---------------------------------------------------------------- Part 3
def extract(T):
    p = T[:q] & MASK; h = T[:q] >> m
    d = np.array([(int(T[a | (1 << m)]) >> m) ^ int(h[a]) for a in range(q)])   # b = 1
    form = bool(np.array_equal(T, p[LO] | ((h[LO] ^ MUL[d[LO], HI]) << m)))
    return p, h, d, form

def hyp(p, d):
    perm = len(set(p.tolist())) == q
    du = max(int(np.bincount(p[np.arange(q) ^ u] ^ p, minlength=q).max()) for u in range(1, q))
    eps = int(d[0]); Kl = d ^ eps
    aff = all(Kl[a ^ b] == Kl[a] ^ Kl[b] for a in range(q) for b in range(q))
    ker = [a for a in range(q) if Kl[a] == 0]
    fib = sorted(set(np.bincount(d, minlength=q).tolist()))
    rho = ker[1] if len(ker) == 2 else None
    pairs = rho is not None and all(sorted([a, a ^ rho]) == sorted(np.nonzero(d == d[a])[0].tolist()) for a in range(q))
    return {'p_perm': perm, 'p_DU': du, 'p_APN': du == 2, 'd_affine': aff, 'ker_K': ker, 'rho': rho,
            'omega': (1 << popc(rho)) if rho else None, 'd_nonvanishing': bool(np.all(d != 0)),
            'd_fibre_sizes': fib, 'fibres_are_pairs_a_a+rho': bool(pairs),
            'H_holds': perm and du == 2 and aff and len(ker) == 2 and bool(np.all(d != 0))}

def S_bound(omega, T=4):
    z = e = Fr(1, q); out = {}
    for t in range(1, T + 1):
        out[t] = max(z, Fr(2, N) + Fr(2, q) * e) * N
        z, e = Fr(2, N) + Fr(2, q) * e, Fr(2 * omega, N) + z / omega + Fr(2, q) * e
    return out

def full_check(name, T, hy):
    out = {}
    out['F_perm'] = len(set(T.tolist())) == N
    CF = ddt(m, T); B = J(T); CB = ddt(m, B)
    rho = hy['rho']; omega = hy['omega']
    cls = np.full(N, 'G', dtype=object); cls[0] = '0'
    cls[(LO == 0) & (IDX != 0)] = 'Z'
    if rho is not None: cls[LO == rho] = 'E'
    Zs, Es, Gs = [np.nonzero(cls == c)[0] for c in 'ZEG']
    unit = np.nonzero(LO != 0)[0]
    # Lemma 0
    out['L0_G_rows_max_CF'] = int(CF[Gs].max()); out['L0_ZE_rows_max_CF'] = int(CF[np.r_[Zs, Es]].max())
    out['L0_ok'] = out['L0_G_rows_max_CF'] <= 2 and out['L0_ZE_rows_max_CF'] <= 2 * q
    # eps(B)
    out['DU_B'] = int(CB[1:].max()); out['eps_B_eq_1_over_q'] = out['DU_B'] == q
    # section 4 table  (counts; bound in counts = bound * N)
    colsum = lambda rows, cols: int(CB[np.ix_(rows, cols)].sum(axis=0).max())
    mx = lambda rows, cols: int(CB[np.ix_(rows, cols)].max())
    tab4 = {'ZtoZ_colsum': (colsum(Zs, Zs), 0), 'ZtoE_colsum': (colsum(Zs, Es), N // omega),
            'EtoZ_colsum': (colsum(Es, Zs), 2 * q), 'EtoE_colsum': (colsum(Es, Es), 2 * q),
            'GtoZ_max': (mx(Gs, Zs), 2), 'GtoE_max': (mx(Gs, Es), 2 * omega),
            'F_EtoUnit_colsum': (int(CF[np.ix_(Es, unit)].sum(axis=0).max()), 2 * q),
            'F_GtoUnit_max': (int(CF[np.ix_(Gs, unit)].max()), 2)}
    out['sec4_table_counts_(value,bound)'] = tab4
    out['sec4_ok'] = all(v <= b for v, b in tab4.values())
    # exact EDP_t, t = 1..4  (float64 exact: all integers < 2^53)
    Bf = CB.astype(np.float64); cur = CF.astype(np.float64); edp = {}
    for t in range(1, 5):
        cur = Bf @ cur
        mxv = cur[1:].max(); assert mxv == np.floor(mxv) and mxv < 2 ** 53
        edp[t] = Fr(int(mxv) * N, N ** (t + 1))
    sb = S_bound(omega)
    out['EDP_xN'] = {t: [str(v), round(float(v), 5)] for t, v in edp.items()}
    out['warmS_bound_xN'] = {t: [str(v), round(float(v), 5)] for t, v in sb.items()}
    out['EDP_le_warmS_all_t'] = all(edp[t] <= sb[t] for t in sb)
    out['EDP2_le_4'] = edp[2] <= 4; out['EDP2_le_6+6/q'] = edp[2] <= 6 + Fr(6, q)
    out['uniform_claim_EDP2'] = '4/N (omega=2)' if omega == 2 else '(6+6/q)/N (general omega)'
    out['uniform_ok'] = (edp[2] <= 4) if omega == 2 else (edp[2] <= 6 + Fr(6, q))
    print('CHECK', name, json.dumps(out, default=str), flush=True)
    return out

def main(outdir):
    t0 = time.time(); os.makedirs(outdir, exist_ok=True)
    out = {'m': m, 'q': q, 'N': N, 'code': 'bits0-4 digit0, bits5-9 digit1'}
    r1, h0tab, ptab, dtab, ppoly = part1(); out['part1_h0_ring_polynomial'] = r1
    r2, invtab = part2(); out['part2_realize_arbitrary_pair'] = r2
    maps = {}
    maps['natural_F'] = np.load(os.path.join(C1, 'data', 'F_m5_r3.npy')).astype(np.int64)
    maps['H_A'] = np.load(os.path.join(C2, 'cost', 'table_H_A_m5.npy')).astype(np.int64)
    maps['H_B'] = np.load(os.path.join(C2, 'cost', 'table_H_B_m5.npy')).astype(np.int64)
    maps['P1theta_fact'] = np.load(os.path.join(C2, 'cost', 'table_P1theta_fact_m5.npy')).astype(np.int64)
    # P1theta sigma-lift (C1 column), rebuilt as in p210
    def trace(x):
        s = 0; y = x
        for _ in range(m): s ^= y; y = int(MUL[y, y])
        return s
    theta = [x for x in range(2, q) if trace(x) == 0][0]
    co = {6: 1}
    for i in range(m):
        c = theta
        for _ in range(i): c = int(MUL[c, c])
        for e in (4, 2, 0): co[(1 << i) + e] = co.get((1 << i) + e, 0) ^ c
    co = {e: c for e, c in co.items() if c}
    maps['P1theta_sigma'] = ring_poly(co)
    maps['h0_lift_witness'] = h0tab
    maps['X30_d0_ringpoly'] = invtab
    d0f = np.array([peval({4: 1, 2: 1, 0: 1}, a) for a in range(q)])
    # d(a) = d0(c a): ker = {0, 1/c}
    def rho_to_c(rho): return finv(rho)
    for tag, rho in (('mainp_rho=t(w1)_randh', 2), ('mainp_rho=wt3_randh', 0b01011)):
        c = rho_to_c(rho); dd = np.array([peval({4: 1, 2: 1, 0: 1}, int(MUL[c, a])) for a in range(q)])
        hh = rng.integers(0, q, q)
        maps[tag] = ptab[LO] | ((hh[LO] ^ MUL[dd[LO], HI]) << m)
    maps['NEG_dickson_g5'] = ring_poly({5: 1, 3: 3 & 1 | ((3 >> 1) << m), 1: 1})
    out['maps'] = {}
    own = {'P1theta_sigma': co, 'P1theta_fact': co, 'natural_F': ppoly}
    for name, T in maps.items():
        p, h, d, form = extract(T)
        rec = {'form_(p(a),h(a)+d(a)b)_all_1024': form}
        hy = hyp(p, d); rec['hypothesis'] = hy
        if name in own:
            dp = pder(own[name]); rec['own_residue_poly_deg'] = max(own[name])
            rec['d_eq_own_formal_derivative'] = all(peval(dp, a) == int(d[a]) for a in range(q))
            rec['own_derivative_exponents'] = {str(e): c for e, c in sorted(dp.items())}
        if name in ('H_A', 'H_B', 'X30_d0_ringpoly') or name.startswith('mainp_rho'):
            rec['residue_eq_main_p'] = bool(np.array_equal(p, ptab)) if name != 'X30_d0_ringpoly' else None
            rec['d_eq_main_pprime'] = bool(np.array_equal(d, dtab))
            rec['d_eq_d0'] = bool(np.array_equal(d, d0f))
        if name == 'X30_d0_ringpoly':
            rec['residue_eq_x^-1'] = bool(all(int(p[a]) == fpow(a, 30) if a else int(p[a]) == 0 for a in range(q)))
        rec['sha256'] = hashlib.sha256(T.astype(np.int64).tobytes()).hexdigest()[:16]
        print('MAP', name, json.dumps(rec, default=str), flush=True)
        if form and hy['H_holds']:
            rec['full'] = full_check(name, T, hy)
        else:
            rec['full'] = 'SKIPPED: hypothesis (p APN perm, d affine 2-to-1 non-vanishing) fails -> no claim'
        out['maps'][name] = rec
    ok = all(True if isinstance(v['full'], str) else
             (v['full']['L0_ok'] and v['full']['eps_B_eq_1_over_q'] and v['full']['sec4_ok'] and
              v['full']['EDP_le_warmS_all_t'] and v['full']['uniform_ok']) for v in out['maps'].values())
    out['ALL_HYP_MAPS_PASS'] = ok; out['seconds'] = round(time.time() - t0, 1)
    json.dump(out, open(os.path.join(outdir, 'p312_results.json'), 'w'), indent=1, default=str)
    print('P312=' + ('PASS' if ok else 'FAIL'), out['seconds'], flush=True)
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
