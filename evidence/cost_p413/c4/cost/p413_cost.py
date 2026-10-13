#!/usr/bin/env python3
"""P4-13 (C4): fair cost counting under ONE rule for the C4 candidate family.

Usage (cwd = apn_cipher/c4/cost):
  python3 -I -B p413_cost.py ../../c2/cost/p210_results.json ../spec/CANDIDATE_P4_SPLIT_TAIL.json ../../c3/spec/CANDIDATE_P3B_THREE.json p413_results.json

Rule (same for every layout):
  local block S_t(x;k_1..k_t) = F(B(...B(B(x)+k_1)...)+k_t), B = J o F  ->  F: t+1, J: t, inner key additions: t  (per word)
  layout (t_1,...,t_r) with r local layers per word, r-1 word mixings M, whitening k0 (w words), and one reset
  key word L_i after each mixing (w words each)  ->
     F = w*sum(t_i+1), J = w*sum(t_i), M = r-1, key additions = w*sum(t_i) + w + (r-1)*w
  (macro MAC (2,2) of C2 has no k0: keys = w*sum t_i + (r-1)*w; listed for reference only.)
Units c_F, c_J, c_M, c_k (one ring key addition on a full 2m-bit word) are symbols.
Exact fractions: (4/N)^w, N = q^2 = 4^m.
PD residue p = x^{-1} = x^(2^m - 2) on F_{2^m}: Itoh-Tsujii chain, verified exhaustively for m = 5, 7.
Bit model (m = 5 only; upper bounds, not minimal circuits): natural F = C2 measured min(45 AND/158 XOR);
F32 schoolbook product 25 AND / 25 XOR (C2 p210); squarings and d0 are F2-linear maps, naive XOR = sum(row weight - 1).
"""
import json, sys, hashlib
from fractions import Fraction as Fr
import sympy as sp

p210, spec_new, spec_p3b, outp = sys.argv[1:5]
R = json.load(open(p210))
SN = json.load(open(spec_new))
SB = json.load(open(spec_p3b))

w, cF, cJ, cM, ck = sp.symbols('w c_F c_J c_M c_k', positive=True)

def counts(layout, k0=True):
    r = len(layout)
    nF = sum(t + 1 for t in layout)
    nJ = sum(layout)
    nK = sum(layout) + (1 if k0 else 0) + (r - 1)
    return dict(F=nF, J=nJ, M=r - 1, K=nK)  # F,J,K are per word (multiply by w); M is absolute

LAY = {'SPLIT_TAIL_(2,2,1,1)': ((2, 2, 1, 1), True), 'P3B_(2,2,2)': ((2, 2, 2), True),
       'THICK_(2,2,2,2)': ((2, 2, 2, 2), True), 'MAC_C2_(2,2)_ref': ((2, 2), False)}
C = {k: counts(*v) for k, v in LAY.items()}

# --- self-check against specs / task statement
assert C['SPLIT_TAIL_(2,2,1,1)'] == dict(F=10, J=6, M=3, K=10), C
assert SN['cost'] == {'F': '10w', 'J': '6w', 'M': 3, 'key_additions': '10w'}, SN['cost']
assert C['P3B_(2,2,2)'] == dict(F=9, J=6, M=2, K=9)
assert C['THICK_(2,2,2,2)'] == dict(F=12, J=8, M=3, K=12)
# S2 = 3F, 2J, 2 keys; S1 = 2F, 1J, 1 key
assert counts((2,), False) == dict(F=3, J=2, M=0, K=2) and counts((1,), False) == dict(F=2, J=1, M=0, K=1)
assert C['MAC_C2_(2,2)_ref'] == dict(F=6, J=4, M=1, K=5)
p3b_txt = json.dumps(SB)

def cost_expr(c):
    return sp.expand(w * (c['F'] * cF + c['J'] * cJ + c['K'] * ck) + c['M'] * cM)

out = {'rule': __doc__.split('Rule')[1].split('Units')[0].strip(), 'counts_per_word': C,
       'cost_symbolic': {k: str(cost_expr(v)) for k, v in C.items()}}
D = {}
pairs = [('SPLIT_TAIL_(2,2,1,1)', 'P3B_(2,2,2)'), ('THICK_(2,2,2,2)', 'SPLIT_TAIL_(2,2,1,1)'),
         ('THICK_(2,2,2,2)', 'P3B_(2,2,2)'), ('P3B_(2,2,2)', 'MAC_C2_(2,2)_ref')]
for a, b in pairs:
    D[a + ' - ' + b] = str(sp.expand(cost_expr(C[a]) - cost_expr(C[b])))
out['differences_symbolic'] = D

# --- exact bound values and widths
tab = []
for m in (5, 7):
    q = 2 ** m; N = q * q
    for ww in (2, 4):
        b = Fr(4, N) ** ww
        tab.append({'m': m, 'w': ww, 'q': q, 'N': N, 'width_bits': 2 * m * ww,
                    'bound_(4/N)^w': str(b), 'log2_bound': -( (2*m - 2) * ww ),
                    'check_log2': b == Fr(1, 2 ** ((2 * m - 2) * ww)),
                    'ideal_2^-width_ratio': str(b * Fr(2 ** (2 * m * ww))),
                    'key_bits_independent_model': {k: C[k]['K'] * ww * 2 * m for k in C}})
assert all(x['check_log2'] for x in tab)
out['bounds_and_widths'] = tab
out['general_width'] = {'block_bits': '2*m*w', 'bound': '(4/N)^w = 2^{-(2m-2)w} (q>=32, independent keys)',
                        'key_bits_independent_model': {k: '%d*w*2m' % C[k]['K'] for k in C},
                        'practical_width_and_key_schedule': 'UNDETERMINED (no key schedule specified; independent-key model only)'}

# --- F_{2^m} arithmetic, Itoh-Tsujii inverse chain
MOD = {5: (1 << 5) | (1 << 2) | 1, 7: (1 << 7) | 2 | 1}  # c2 GR(4,5)=Z4[t]/(t^5+t^2+1); c1 ringlib m7: 1+t+t^7

def gmul(a, b, m):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> m & 1: a ^= MOD[m]
    return r

def gsq_k(a, k, m):
    for _ in range(k): a = gmul(a, a, m)
    return a

def itoh_tsujii(m):
    """x^{2^{m-1}-1} by the binary method on e = m-1, then one squaring. Returns (mults, sq, chain, fn)."""
    e = m - 1; bits = bin(e)[2:]
    steps = []  # (k_squarings, multiply_by) ; b_j denotes x^{2^j - 1}
    j = 1
    for bit in bits[1:]:
        steps.append(('b%d=b%d^(2^%d)*b%d' % (2 * j, j, j, j), j, 'self')); j = 2 * j
        if bit == '1':
            steps.append(('b%d=b%d^2*x' % (j + 1, j), 1, 'x')); j += 1
    assert j == e
    mults = len(steps); sq = sum(s[1] for s in steps) + 1
    def f(x):
        b = x; jj = 1
        for name, k, typ in steps:
            b = gmul(gsq_k(b, k, m), b if typ == 'self' else x, m)
        return gmul(b, b, m)
    return mults, sq, [s[0] for s in steps] + ['inv=b%d^2' % e], f, steps

inv = {}
for m in (5, 7):
    mu, sq, chain, f, steps = itoh_tsujii(m)
    ok = all(gmul(x, f(x), m) == 1 for x in range(1, 2 ** m)) and f(0) == 0
    pw = all(f(x) == gsq_k(x, 0, m) or True for x in range(1))
    # direct power check x^(2^m-2)
    def powm(x, e):
        r = 1
        while e:
            if e & 1: r = gmul(r, x, m)
            x = gmul(x, x, m); e >>= 1
        return r
    ok2 = all(powm(x, 2 ** m - 2) == f(x) for x in range(2 ** m))
    from math import floor, log2
    itt_formula = floor(log2(m - 1)) + bin(m - 1).count('1') - 1
    assert ok and ok2 and mu == itt_formula and sq == m - 1
    inv[m] = {'mults': mu, 'squarings': sq, 'chain': chain, 'verified_all_elements': ok and ok2,
              'ITT_formula_floorlog2(m-1)+HW(m-1)-1': itt_formula, 'modulus_int': MOD[m], 'steps': steps}

# APN check of x^{-1} for m=5,7 (differential uniformity 2), and even m=4,6 would be 4 (not used)
def du(m):
    q = 2 ** m; best = 0
    for a in range(1, q):
        cnt = {}
        for x in range(q):
            y = inv[m]['fn'](x) ^ inv[m]['fn'](x ^ a) if 'fn' in inv[m] else None
            cnt[y] = cnt.get(y, 0) + 1
        best = max(best, max(cnt.values()))
    return best
for m in (5, 7):
    inv[m]['fn'] = itoh_tsujii(m)[3]
    inv[m]['differential_uniformity'] = du(m)
    assert inv[m]['differential_uniformity'] == 2
    del inv[m]['fn']

# linear-map naive XOR counts over F_2 (m = 5 and 7)
def lin_xor(fun, m):
    cols = [fun(1 << i) for i in range(m)]
    tot = 0
    for r in range(m):
        wgt = sum((c >> r) & 1 for c in cols)
        tot += max(wgt - 1, 0)
    return tot

bitlin = {}
for m in (5, 7):
    sqmaps = {k: lin_xor(lambda x, k=k: gsq_k(x, k, m), m) for k in sorted({s[1] for s in inv[m]['steps']} | {1})}
    d0_lin = lin_xor(lambda a: gsq_k(a, 2, m) ^ gsq_k(a, 1, m), m)  # d0(a) = a^4 + a^2 + 1 : linear part a^4+a^2, +1 is NOT on bit 0
    bitlin[m] = {'squaring_map_naive_XOR': sqmaps, 'd0_linear_part_naive_XOR': d0_lin, 'd0_constant_NOT': 1}

# bit model m = 5
F32 = R['INV1024_chain']['F32_mult_schoolbook']; assert F32 == {'AND': 25, 'XOR': 25}
nat = R['sboxes']['P53_natural']['bit_full_ANF']; assert (nat['AND'], nat['XOR']) == (45, 158)
KEY = R['bit_key_add']; assert (KEY['AND'], KEY['XOR']) == (5, 15)
MX = R['mixers']
m = 5; st = inv[5]['steps']
pd_and = (inv[5]['mults'] + 1) * F32['AND']           # chain mults + product d0(a)*b
pd_xor = (inv[5]['mults'] + 1) * F32['XOR'] + sum(bitlin[5]['squaring_map_naive_XOR'][s[1]] for s in st) \
         + bitlin[5]['squaring_map_naive_XOR'][1] + bitlin[5]['d0_linear_part_naive_XOR']
PD = {'AND': pd_and, 'XOR': pd_xor, 'NOT': 1,
      'formula': '(ITT mults + 1 product) x F32 schoolbook + naive XOR of squaring maps + d0 linear part; h0 = 0 costs nothing',
      'status': 'upper bound for ONE circuit; residue x^{-1}, d = d0, h = 0 (PD_ROLES_H0_P3 sec.2.1 witness)'}
units5 = {'F_natural': {'AND': 45, 'XOR': 158}, 'F_PD_inv_d0_h0': {'AND': pd_and, 'XOR': pd_xor},
          'J': {'AND': 0, 'XOR': 0}, 'key_add_ring_2m': {'AND': 5, 'XOR': 15},
          'M': {k: MX[k]['bit'] for k in MX}}

def bit_total(c, ww, Fu, Mlist):
    a = ww * (c['F'] * Fu['AND'] + c['K'] * 5) + sum(MX[x]['bit']['AND'] for x in Mlist)
    x_ = ww * (c['F'] * Fu['XOR'] + c['K'] * 15) + sum(MX[x]['bit']['XOR'] for x in Mlist)
    return {'AND': a, 'XOR': x_}

bit_rows = []
cfg = {2: {'A_all_MDS_alt': 'MDS_alt_2x2', 'B_M1_MDS_alt_M2M3_M2': None},
       4: {'L_C_substitute_for_Cauchy4': 'L_C_4x4'}}
for k, c in C.items():
    for ww in (2, 4):
        for cname, mx in cfg[ww].items():
            if mx is None:
                if c['M'] == 0: continue
                Ml = ['MDS_alt_2x2'] + ['M2_2x2'] * (c['M'] - 1)
            else:
                Ml = [mx] * c['M']
            for Fn in ('F_natural', 'F_PD_inv_d0_h0'):
                bit_rows.append({'layout': k, 'm': 5, 'w': ww, 'mixers': cname, 'Mlist': Ml, 'F': Fn,
                                 'bit_upper': bit_total(c, ww, units5[Fn], Ml)})

# Feistel local comparison (same 2m-bit block); no ranking claimed
fe = {'model': '3-round balanced Feistel on 2m bits, f: F_q -> F_q APN permutation (x^{-1}, m odd), XOR round keys, independent',
      'bound_proven_read': 'NK J.Cryptology 8(1995) Thm 2 (WebFetch summary only): s>=3 (proof written for s=3), <= 2p^2 = 8/N with p = 2/q',
      'bound_AO_unconfirmed': 'Aoki-Ohta 1997: abstract says p^2-type strict bound for bijective F and "more than 3 rounds"; full text 403 -> 4/N at 3 rounds NOT asserted',
      'ours_local_S2': 'W2: <= 4/N (all lifts, q>=32) for S2 = 3F + 2J + 2 ring key additions on one 2m-bit word',
      'counts': {'Feistel3': {'f(m-bit)': 3, 'xor_key(m-bit)': 3, 'xor_data(m-bit)': 3}, 'S2': {'F(2m-bit word)': 3, 'J': 2, 'ring_key_add(2m-bit)': 2}},
      'bit_m5_with_inverse': {
          'Feistel3_f=x^-1': {'AND': 3 * inv[5]['mults'] * F32['AND'],
                              'XOR': 3 * (inv[5]['mults'] * F32['XOR'] + sum(bitlin[5]['squaring_map_naive_XOR'][s[1]] for s in st) + bitlin[5]['squaring_map_naive_XOR'][1]) + 3 * 5 + 3 * 5},
          'Feistel3_f=x^3': {'AND': 3 * F32['AND'], 'XOR': 3 * (F32['XOR'] + bitlin[5]['squaring_map_naive_XOR'][1]) + 3 * 5 + 3 * 5,
                             'note': 'x^3 = x^2*x: 1 squaring (linear) + 1 product; APN permutation for odd m (checked below)'},
          'S2_PD_inv': {'AND': 3 * pd_and + 2 * 5, 'XOR': 3 * pd_xor + 2 * 15},
          'S2_natural': {'AND': 3 * 45 + 2 * 5, 'XOR': 3 * 158 + 2 * 15}},
      'reading': 'Different guarantees (8/N proven vs 4/N), different key groups (XOR m-bit vs Z4-ring 2m-bit), different component widths; no ranking by call count.'}
def cube_check(m):
    q = 2 ** m; cube = [gmul(gmul(x, x, m), x, m) for x in range(q)]
    perm = len(set(cube)) == q
    du_ = max(max({(cube[x] ^ cube[x ^ a]): 0 for x in range(q)} and [sum(1 for x in range(q) if cube[x] ^ cube[x ^ a] == y) for y in range(q)]) for a in range(1, q))
    return {'permutation': perm, 'differential_uniformity': du_}
fe['x^3_check'] = {m_: cube_check(m_) for m_ in (5, 7)}
assert all(v['permutation'] and v['differential_uniformity'] == 2 for v in fe['x^3_check'].values())
out['inverse_chain'] = inv
out['linear_maps_naive_XOR'] = bitlin
out['bit_units_m5'] = units5
out['PD_F_bit_m5'] = PD
out['bit_rows_m5'] = bit_rows
out['feistel_local_comparison'] = fe
out['inputs_sha256'] = {pth: hashlib.sha256(open(pth, 'rb').read()).hexdigest() for pth in (p210, spec_new, spec_p3b)}
json.dump(out, open(outp, 'w'), indent=1, ensure_ascii=False, default=str)

print('counts', C)
for k, v in out['cost_symbolic'].items(): print('COST', k, v)
for k, v in D.items(): print('DIFF', k, '=', v)
for x in tab: print('BOUND m=%d w=%d width=%d bound=%s log2=%d keybits=%s' % (x['m'], x['w'], x['width_bits'], x['bound_(4/N)^w'], x['log2_bound'], x['key_bits_independent_model']))
for m_ in (5, 7): print('INV m=%d mults=%d sq=%d chain=%s verified=%s DU=%d' % (m_, inv[m_]['mults'], inv[m_]['squarings'], inv[m_]['chain'], inv[m_]['verified_all_elements'], inv[m_]['differential_uniformity']))
print('LIN', bitlin)
print('PD_F_bit_m5', PD['AND'], PD['XOR'])
for r in bit_rows: print('BIT', r['layout'], 'w=%d' % r['w'], r['mixers'], r['F'], r['bit_upper'])
print('FEISTEL', json.dumps(fe['bit_m5_with_inverse']), fe['x^3_check'])
print('P413=PASS')
