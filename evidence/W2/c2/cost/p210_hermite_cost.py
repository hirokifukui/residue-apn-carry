#!/usr/bin/env python3
"""p210_hermite_cost.py -- P2-10 (C2, Claude 2026-10-09).  m = 5, r = 3 only.  New file; c1/ is read only.

1. Hermite control H_p = p + (X^q - X)(d0 + p') in F_q[X], p = reduced (deg < q) representative of P_{5,3},
   d0 = X^4 + X^2 + 1.  Checks: H_p(a) = p(a) on F_q, formal derivative H_p' = d0, red(H_p) = p, deg H_p >= q,
   d0 has no zero on F_32 and only two-point fibres.
   Two coefficient lifts to R = GR(4,5) = Z4[t]/(t^5+t^2+1) (code: bits 0-4 digit 0, bits 5-9 digit 1):
     H_A  "sigma-coefficient lift": every F_q coefficient c (expanded, reduced H_p) is replaced by sigma(c) =
          the element of R whose t-coefficients are the 0/1 bits of c (digit 1 = 0).  No Teichmueller lift.
     H_B  "formula lift": sigma(p) + (X^q - X) * sigma(d0 + p') multiplied out in R[X] (integer coefficients mod 4;
          here every F_q coefficient is 0 or 1, asserted).
   Both: F-table, permutation of R, residue = p, high digit = h(a) xor d0(a) b, ring DU, DU of J o H, exact EDP.
2. Ring evaluation formulas (op-counted by an instrumented evaluator, and checked equal to the tables):
   natural F (Prop C form), H_A, H_B, Dickson g5 = X (X^4 + 3X^2 + 1), P1theta factored form (= a THIRD lift of the
   P1theta residue, not the C1 sigma-lift table; both kept as separate columns).
   F_{2^10} inversion: Itoh-Tsujii chain x^(2^10-2) with 4 multiplications + 9 squarings, checked against the table.
3. Bit model (upper bounds with explicit circuits): (i) full 10-bit ANF circuit with shared monomials
   (AND = monomials of degree >= 2 in a greedy chain set, XOR = sum over output bits of (#non-constant monomials - 1),
   NOT = output bits with constant term 1); (ii) for maps of the form (p(a), h(a) xor d(a) b): ANF circuit of the
   15 a-only bits (p, h, d) + schoolbook F_32 product d(a) b (25 AND, 16 + reduction XOR) + 5 XOR.
   F_1024 schoolbook multiplication and multi-squaring XOR counts for the inversion chain.  Ring key addition and
   ring constant multiplications in the bit model, also by explicit circuits.
4. Exact key-averaged EDP x N (one word, model of C1 t313: X_i = J(S(X_{i-1})) + K_i, Y = S(X_t)), t = 0..6, CRT.
usage: python3 -I p210_hermite_cost.py OUTDIR
"""
import sys, os, json, hashlib, time
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
C1 = os.path.normpath(os.path.join(HERE, '..', '..', 'c1'))
sys.path.insert(0, os.path.join(C1, 'code'))
from codes import mk
from ringlib import GR4, GF2m, P_exponents
from ddt import ddt, PRIMES, modmat, mulmod, crt

m, q, N = 5, 32, 1024
MASK = q - 1
add, neg, sub, J = mk(m)
R = GR4(m); K = GF2m(m); MUL = K.MUL
IDX = np.arange(N, dtype=np.int64)
LO, HI = IDX & MASK, IDX >> m


def popc(x): return bin(int(x)).count('1')
def zcode(c): c %= 4; return (c & 1) | ((c >> 1) << m)
def cvec(code): return R.decode(np.array([code], dtype=np.int64))[0]


def ring_poly(coeffs):
    """coeffs: dict exponent -> ring element code. Horner over all of R. Returns code table."""
    deg = max(coeffs); acc = np.zeros_like(R.all)
    for e in range(deg, -1, -1):
        acc = R.mul(acc, R.all)
        if e in coeffs:
            acc = (acc + cvec(coeffs[e])) % 4
    return R.encode(acc)

# ---------------- F_q[X] arithmetic (coefficients = F_32 ints) ----------------
def padd(A, B):
    C = dict(A)
    for e, c in B.items(): C[e] = C.get(e, 0) ^ c
    return {e: c for e, c in C.items() if c}
def pmul(A, B):
    C = {}
    for e1, c1 in A.items():
        for e2, c2 in B.items():
            C[e1 + e2] = C.get(e1 + e2, 0) ^ int(MUL[c1, c2])
    return {e: c for e, c in C.items() if c}
def pder(A):  # char 2: d/dX c X^e = (e mod 2) c X^(e-1)
    return {e - 1: c for e, c in A.items() if e % 2 == 1}
def peval(A, a):
    s = 0
    for e, c in A.items(): s ^= int(MUL[c, K.pow(a, e)])
    return s
def pred(A):  # reduce modulo X^q - X (exponent e >= q -> e - (q-1)), keeps X^0 separate from X^(q-1)
    C = {}
    for e, c in A.items():
        while e >= q: e -= (q - 1)
        C[e] = C.get(e, 0) ^ c
    return {e: c for e, c in C.items() if c}
def trace(x):
    s = 0; y = x
    for _ in range(m): s ^= y; y = int(MUL[y, y])
    return s

# ---------------- instrumented ring evaluator ----------------
class Ev:
    def __init__(s): s.c = {'mu': 0, 's': 0, 'kappa': 0, 'alpha': 0}
    def mul(s, x, y): s.c['mu'] += 1; return R.mul(x, y)
    def sq(s, x): s.c['s'] += 1; return R.mul(x, x)
    def cmul(s, code, x): s.c['kappa'] += 1; return R.mul(cvec(code), x)
    def add(s, x, y): s.c['alpha'] += 1; return (x + y) % 4
    def sub(s, x, y): s.c['alpha'] += 1; return (x - y) % 4
    def addc(s, x, code): s.c['alpha'] += 1; return (x + cvec(code)) % 4

def ev_nat(ev, keep=False):
    X = R.all
    X2 = ev.sq(X); X4 = ev.sq(X2); X8 = ev.sq(X4); X16 = ev.sq(X8)
    VW = ev.add(X, X2); VWZ = ev.add(VW, X16); WY = ev.add(X2, X8)
    P = ev.mul(WY, VWZ); out = ev.add(VW, P); out = ev.sub(out, X4)   # V + W - W^2 + (W+Y)(V+W+Z)
    return (out, dict(X=X, X2=X2, X4=X4, X8=X8, X16=X16)) if keep else out
def ev_HB(ev):
    P, s = ev_nat(ev, True)
    X32 = ev.sq(s['X16']); A = ev.sub(X32, s['X']); Bq = ev.add(s['X8'], s['X4'])
    return ev.add(P, ev.mul(A, Bq))                                  # sigma(p) + (X^32 - X)(X^8 + X^4)
def ev_HA(ev):
    P, s = ev_nat(ev, True)
    T1 = ev.mul(s['X'], ev.sub(s['X4'], s['X8']))                    # X^5 - X^9
    X32 = ev.sq(s['X16']); T2 = ev.mul(X32, ev.add(s['X8'], s['X4']))  # X^40 + X^36
    return ev.add(ev.add(P, T1), T2)
def ev_D5(ev):
    X = R.all; X2 = ev.sq(X); X4 = ev.sq(X2)
    T = ev.add(X4, ev.cmul(zcode(3), X2)); T = ev.addc(T, zcode(1))
    return ev.mul(X, T)                                              # X (X^4 + 3 X^2 + 1)
def ev_P1fact(ev, consts):
    X = R.all; Xp = [X]
    for _ in range(m - 1): Xp.append(ev.sq(Xp[-1]))                  # X^(2^i), i = 0..4
    L = ev.cmul(consts[0], Xp[0])
    for i in range(1, m): L = ev.add(L, ev.cmul(consts[i], Xp[i]))
    d = ev.addc(ev.add(Xp[2], Xp[1]), zcode(1))
    X6 = ev.mul(Xp[1], Xp[2])
    return ev.add(X6, ev.mul(d, L))                                  # X^6 + (X^4+X^2+1) L_theta, lifted constants

# ---------------- F_1024 ----------------
G10 = (1 << 10) | (1 << 3) | 1
def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a & 1024: a ^= G10
    return r
def gf1024_inv():
    inv = [0] * 1024
    for a in range(1, 1024):
        for b in range(1, 1024):
            if gmul(a, b) == 1: inv[a] = b; break
    return np.array(inv, dtype=np.int64)
def gsqk(a, k):
    for _ in range(k): a = gmul(a, a)
    return a
def inv_chain(x):
    b1 = x; b2 = gmul(gsqk(b1, 1), b1); b4 = gmul(gsqk(b2, 2), b2); b8 = gmul(gsqk(b4, 4), b4)
    b9 = gmul(gsqk(b8, 1), x); return gsqk(b9, 1)                   # x^(2^10 - 2): 4 mults, 1+2+4+1+1 = 9 squarings
def linmap_xor(fn, n):
    cols = [fn(1 << i) for i in range(n)]
    rows = [sum(((cols[i] >> j) & 1) << i for i in range(n)) for j in range(n)]
    return sum(max(popc(r) - 1, 0) for r in rows)

# ---------------- ANF / bit circuits ----------------
def anf(table, nin, nout):
    table = np.asarray(table, dtype=np.int64); out = []
    for j in range(nout):
        f = ((table >> j) & 1).astype(np.uint8).copy()
        for i in range(nin):
            f = f.reshape(-1, 2, 1 << i); f[:, 1, :] ^= f[:, 0, :]; f = f.reshape(-1)
        g = f.copy()                                                  # Moebius is an involution: check
        for i in range(nin):
            g = g.reshape(-1, 2, 1 << i); g[:, 1, :] ^= g[:, 0, :]; g = g.reshape(-1)
        assert np.array_equal(g, ((table >> j) & 1).astype(np.uint8))
        out.append(set(np.nonzero(f)[0].tolist()))
    return out
def and_chain(monos):
    built = {u for u in monos if popc(u) >= 2}
    maxd = max((popc(u) for u in built), default=0)
    for k in range(maxd, 2, -1):
        need = [u for u in built if popc(u) == k and not any(((u >> i) & 1) and (u ^ (1 << i)) in built for i in range(20))]
        while need:
            cnt = {}
            for u in need:
                for i in range(20):
                    if (u >> i) & 1: cnt[u ^ (1 << i)] = cnt.get(u ^ (1 << i), 0) + 1
            best = max(cnt, key=lambda s_: (cnt[s_], -s_)); built.add(best)
            need = [u for u in need if not any(((u >> i) & 1) and (u ^ (1 << i)) == best for i in range(20))]
    # verify every built monomial of degree >= 3 has a built parent
    for u in built:
        if popc(u) >= 3: assert any(((u >> i) & 1) and (u ^ (1 << i)) in built for i in range(20))
    return built
def circuit(table, nin, nout):
    bits = anf(table, nin, nout); allm = set().union(*bits)
    ch = and_chain(allm)
    xor = sum(max(len([u for u in b if u != 0]) - 1, 0) for b in bits)
    nots = sum(1 for b in bits if 0 in b and len(b) > 1)
    deg = max(popc(u) for u in allm)
    return {'AND': len(ch), 'XOR': xor, 'NOT': nots, 'alg_degree': deg}

F32_RED_XOR = sum(popc(K.pow(2, j)) for j in range(m, 2 * m - 1))   # t^5..t^8 mod f folded back
F32_PROD = {'AND': m * m, 'XOR': (m * m - (2 * m - 1)) + F32_RED_XOR}

# ---------------- analysis of one S-box ----------------
def edp_exact(S, T=6):
    CB = ddt(m, J(S)); CF = ddt(m, S)
    primes = PRIMES[:6]
    Bp = [modmat(CB, p) for p in primes]; cur = [modmat(CF, p) for p in primes]
    out = []
    for t in range(T + 1):
        ex, Mod = crt([c.astype(np.int64) for c in cur], primes)
        assert N ** (t + 1) < Mod
        mx = int(ex[1:].max())
        out.append(Fr(mx * N, N ** (t + 1)))
        cur = [mulmod(b, c, p) for b, c, p in zip(Bp, cur, primes)]
    return out, int(CF[1:].max()), int(CB[1:].max())

def residue_info(S, Gpoly=None):
    res = S & MASK
    fa = bool(np.all(res == res[LO]))                                 # residue depends on a only
    p = res[:q]
    info = {'residue_function_of_a_only': fa, 'residue_perm': len(set(p.tolist())) == q}
    info['residue_DU'] = int(max(np.bincount(p[np.arange(q) ^ u] ^ p, minlength=q).max() for u in range(1, q)))
    info['residue_alg_degree'] = circuit(p, m, m)['alg_degree']
    if Gpoly is not None:
        assert all(peval(Gpoly, a) == int(p[a]) for a in range(q))
        dpoly = pder(Gpoly); d = np.array([peval(dpoly, a) for a in range(q)], dtype=np.int64)
        h = S[:q] >> m
        pred_tab = p[LO] | ((h[LO] ^ MUL[d[LO], HI]) << m)
        info['high_digit_eq_h_xor_d_b'] = bool(np.array_equal(pred_tab, S))
        info['d_poly_Fq'] = {str(e): c for e, c in sorted(dpoly.items())}
        eps = int(d[0]); Kl = d ^ eps
        lin = all(Kl[a ^ b] == Kl[a] ^ Kl[b] for a in range(q) for b in range(q))
        ker = [a for a in range(q) if Kl[a] == 0]
        info['d_hypothesisH'] = {'affine': lin, 'nonvanishing': bool(np.all(d != 0)),
                                 'fibre_sizes': sorted(set(np.bincount(d, minlength=q).tolist())),
                                 'ker_K': ker, 'eps': eps, 'eps_notin_ImK': eps not in set(Kl.tolist()),
                                 'omega': (1 << popc(ker[1])) if len(ker) == 2 else None}
        info['_a_part'] = (p, h, d)
    return info

def structured_circuit(p, h, d):
    tab = p | (h << m) | (d << (2 * m))
    c = circuit(tab, m, 3 * m)
    return {'AND': c['AND'] + F32_PROD['AND'], 'XOR': c['XOR'] + F32_PROD['XOR'] + m, 'NOT': c['NOT'],
            'a_part': c, 'F32_product': F32_PROD, 'combine_xor': m}

def main(outdir):
    t0 = time.time(); os.makedirs(outdir, exist_ok=True)
    out = {'m': m, 'q': q, 'N': N, 'ring': 'GR(4,5)=Z4[t]/(t^5+t^2+1)', 'code': 'bits0-4 digit0, bits5-9 digit1'}
    # ---- 1. H_p over F_q ----
    pexp = sorted(P_exponents(m, 3)); assert max(pexp) < q
    p = {e: 1 for e in pexp}; d0 = {4: 1, 2: 1, 0: 1}
    dp = pder(p); Hp = padd(p, pmul({q: 1, 1: 1}, padd(d0, dp)))
    chk = {'p_exponents': pexp, 'p_prime': sorted(dp), 'd0_plus_p_prime': sorted(padd(d0, dp)),
           'H_p_exponents': sorted(Hp), 'H_p_coeffs_all_one': all(c == 1 for c in Hp.values()),
           'deg_H_p': max(Hp), 'deg_ge_q': max(Hp) >= q,
           'H_p_values_eq_p_on_Fq': all(peval(Hp, a) == peval(p, a) for a in range(q)),
           'formal_derivative_H_p': sorted(pder(Hp)), 'H_p_prime_eq_d0': pder(Hp) == d0,
           'red_H_p_eq_p': pred(Hp) == p,
           'd0_zeros_on_Fq': [a for a in range(q) if peval(d0, a) == 0],
           'd0_fibre_sizes': sorted(set(np.bincount([peval(d0, a) for a in range(q)], minlength=q).tolist()))}
    assert chk['H_p_prime_eq_d0'] and chk['H_p_values_eq_p_on_Fq'] and chk['red_H_p_eq_p'] and not chk['d0_zeros_on_Fq']
    out['H_p_Fq'] = chk; print('H_p', chk, flush=True)
    # ---- lifts ----
    assert all(c == 1 for c in Hp.values()) and all(c == 1 for c in p.values())
    HA_coeffs = {e: c for e, c in Hp.items()}                          # sigma(c): code c, digit 1 = 0
    Zp = {e: 1 for e in p}; Zd = {e: 1 for e in padd(d0, dp)}
    HBz = dict(Zp)
    for e, c in Zd.items():
        HBz[e + q] = (HBz.get(e + q, 0) + c) % 4; HBz[e + 1] = (HBz.get(e + 1, 0) - c) % 4
    HB_coeffs = {e: zcode(c) for e, c in HBz.items() if c % 4}
    out['lift_definitions'] = {
        'H_A_sigma_coefficient_lift': {'Z4_coeffs': {str(e): 1 for e in sorted(HA_coeffs)},
                                       'rule': 'each F_q coefficient c -> sigma(c), t-coefficients = bits of c, digit 1 = 0'},
        'H_B_formula_lift': {'Z4_coeffs': {str(e): HBz[e] % 4 for e in sorted(HBz) if HBz[e] % 4},
                             'rule': 'sigma(p) + (X^q - X) sigma(d0 + p\') multiplied out in Z4[X]'},
        'difference_H_A_minus_H_B': '2 X^5'}
    F = np.load(os.path.join(C1, 'data', 'F_m5_r3.npy')).astype(np.int64)
    S = {'P53_natural': F}
    assert np.array_equal(ring_poly({e: 1 for e in pexp}), F)
    S['H_A'] = ring_poly(HA_coeffs); S['H_B'] = ring_poly(HB_coeffs)
    o = json.load(open(os.path.join(C1, 'data', 't303_oracle.json')))[0]
    pt, dt = np.array(o['p_table']), np.array(o['d_table'])
    S['P53_h0'] = pt[LO] | (MUL[dt[LO], HI] << m)
    S['D5'] = ring_poly({5: 1, 3: zcode(3), 1: 1})
    theta = [x for x in range(2, q) if trace(x) == 0][0]
    co = {6: 1}; consts = []
    for i in range(m):
        c = theta
        for _ in range(i): c = int(MUL[c, c])
        consts.append(c)
        for e in (4, 2, 0):
            co[(1 << i) + e] = co.get((1 << i) + e, 0) ^ c
    co = {e: c for e, c in co.items() if c}
    S['P1theta_sigma'] = ring_poly(co)                                   # = C1 t313 'P1theta' (sigma-coefficient lift)
    INV = gf1024_inv(); S['INV1024'] = INV
    S['RANDOM'] = np.random.default_rng(20261014).permutation(N).astype(np.int64)
    # ---- 2. ring formulas, op counts, equality with tables ----
    ring = {}
    for name, fn, ref in [('P53_natural', lambda e: ev_nat(e), F), ('H_A', ev_HA, S['H_A']), ('H_B', ev_HB, S['H_B']),
                          ('D5', ev_D5, S['D5']), ('P1theta_fact', lambda e: ev_P1fact(e, consts), None)]:
        ev = Ev(); tab = R.encode(fn(ev))
        if ref is not None:
            assert np.array_equal(tab, ref), name
        else:
            S['P1theta_fact'] = tab
        ring[name] = dict(ev.c, formula_equals_table=ref is not None)
        print('ring', name, ev.c, flush=True)
    ring['P1theta_sigma'] = {'mu': 2, 's': m - 1, 'kappa': m, 'alpha': 2 * m, 'source': 'C1 COST_MODEL.md count (upper bound, not re-derived here; the factored formula evaluates a DIFFERENT lift = P1theta_fact)'}
    out['theta'] = theta; out['P1theta_consts_sigma'] = consts
    out['ring_cost_per_Sbox'] = ring
    # INV chain
    assert all(inv_chain(x) == int(INV[x]) for x in range(N))
    sq_xor = {k: linmap_xor(lambda a, k=k: gsqk(a, k), 10) for k in (1, 2, 4)}
    red10 = 0
    for j in range(10, 19):
        v = 1 << j
        for i in range(18, 9, -1):
            if (v >> i) & 1: v ^= G10 << (i - 10)
        red10 += popc(v)
    mul1024 = {'AND': 100, 'XOR': (100 - 19) + red10}
    inv_bits = {'AND': 4 * mul1024['AND'], 'XOR': 4 * mul1024['XOR'] + 3 * sq_xor[1] + sq_xor[2] + sq_xor[4], 'NOT': 0,
                'chain': 'b2=b1^2*b1, b4=b2^(2^2)*b2, b8=b4^(2^4)*b4, b9=b8^2*x, inv=b9^2: 4 mult, squarings as 3x(k=1), 1x(k=2), 1x(k=4) linear maps',
                'F1024_mult_schoolbook': mul1024, 'multisquare_xor': sq_xor,
                'karatsuba_one_level_AND': 4 * 75, 'karatsuba_note': '3 products of 5x5 (25 AND each); XOR not counted'}
    out['INV1024_chain'] = {'verified_all_1024': True, 'ring_model': '4 F_1024 multiplications + 9 Frobenius squarings (F_2-linear); not a GR(4,5) polynomial',
                            'bit_schoolbook': inv_bits, 'F32_mult_schoolbook': {'AND': 25, 'XOR': F32_PROD['XOR']}}
    print('INV chain', inv_bits, flush=True)
    # ---- residue / structure / DU / EDP / bit circuits ----
    polys = {'P53_natural': p, 'H_A': Hp, 'H_B': Hp, 'D5': {5: 1, 3: 1, 1: 1}, 'P1theta_sigma': co, 'P1theta_fact': co,
             'P53_h0': None}
    res = {}
    for name, tab in S.items():
        tab = np.asarray(tab, dtype=np.int64)
        r = {'bijective_on_R': len(np.unique(tab)) == N, 'table_sha256_int64': hashlib.sha256(tab.tobytes()).hexdigest()}
        G = polys.get(name)
        if name in polys and G is not None or name == 'P53_h0':
            ri = residue_info(tab, G if name != 'P53_h0' else p)
            pa = ri.pop('_a_part', None)
            r.update(ri)
            if pa is not None:
                r['bit_structured'] = structured_circuit(*pa)
        elif name != 'INV1024' and name != 'RANDOM':
            pass
        r['bit_full_ANF'] = circuit(tab, 2 * m, 2 * m)
        ser, du, duB = edp_exact(tab)
        r['ring_DU_count'] = du; r['DU_count_J_o_S'] = duB
        r['EDP_times_N_withJ_t0..6'] = [str(x) for x in ser]
        r['EDP_times_N_withJ_float'] = [float(x) for x in ser]
        res[name] = r
        print(name, {k: v for k, v in r.items() if k not in ('table_sha256_int64',)}, '%.0fs' % (time.time() - t0), flush=True)
        if name in ('H_A', 'H_B', 'P1theta_fact'):
            np.save(os.path.join(outdir, 'table_%s_m5.npy' % name), tab)
    out['sboxes'] = res
    # ---- bit model: ring key addition, constant multiplications, mixers ----
    out['bit_key_add'] = {'AND': m, 'XOR': 3 * m, 'NOT': 0, 'source': 'c1/code/codes.py add(): lo = a^c, hi = x_hi^y_hi^(a&c)'}
    mixers = {'MDS_alt_2x2': [[1, 1], [1, 2]], 'M2_2x2': [[618, 716], [716, 422]],
              'L_C_4x4': json.load(open(os.path.join(C1, 'spec', 'CANDIDATE_P1_40.json')))['L_C_codes']}
    mres = {}
    cm_cache = {}
    for nm, Mx in mixers.items():
        AND = XOR = NOT = 0; kappa = alpha = 0
        for row in Mx:
            nz = [c for c in row if c]
            for c in nz:
                if c == 1: continue
                kappa += 1
                if c not in cm_cache:
                    cm_cache[c] = circuit(R.encode(R.mul(cvec(c), R.all)), 2 * m, 2 * m)
                AND += cm_cache[c]['AND']; XOR += cm_cache[c]['XOR']; NOT += cm_cache[c]['NOT']
            alpha += len(nz) - 1
            AND += (len(nz) - 1) * m; XOR += (len(nz) - 1) * 3 * m
        mres[nm] = {'ring': {'kappa': kappa, 'alpha': alpha}, 'bit': {'AND': AND, 'XOR': XOR, 'NOT': NOT}, 'codes': Mx}
    out['mixers'] = mres; out['const_mult_bit'] = {str(k): v for k, v in cm_cache.items()}
    print('mixers', {k: (v['ring'], v['bit']) for k, v in mres.items()}, flush=True)
    json.dump(out, open(os.path.join(outdir, 'p210_results.json'), 'w'), indent=1)
    print('P210=PASS %.0fs' % (time.time() - t0))

if __name__ == '__main__':
    main(sys.argv[1])
