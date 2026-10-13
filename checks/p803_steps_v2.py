"""p803_steps_v2.py -- C9 revision of p803_steps.py (finding C8-F03).
Usage: python3 -I -B p803_steps_v2.py OUT.json
Fault injection (must FAIL with nonzero exit): environment P803_FAULT_C=1, or argv flag --fault-C1;
both replace the fixed constant C = 489/50 by C = 1.

Overall verdict: ok = A_ok and B_ok and C_ok (C8 version used only A and C).

(A) exact rational checks of the elementary inequalities of the general 14+1 step argument, m = 5..61
    (unchanged logic, imported from the byte-identical C8 copy p803_steps.py), plus explicit equality checks
    of the general constants (8/5)*10^6 = 1600000 and 1 + (1779/256)*1600000 = 11118751.
(B) inverse map with d of d0 type (Corollary inv13 of the paper):
    B1  for every m = 5..201 the outward upper bound of theta_2/u (u = q^-1/2) is < C, C = 489/50 fixed;
    B2  C = 489/50 equals the C8 rounding rule applied to the m = 5..201 maximum (consistency);
    B3  K_C = max(C + 24/5, 14/5 + 2C/5 + C^2/5) = 323021/12500 exactly;
    B4  sqrt(2) K_C^3 < 24405 and 1 + (1779/256) sqrt(2) K_C^3 < 169597 with outward-rounded sqrt(2);
    B5  (calibration only) on m = 5..201 the three terms eta_rss/u, (nu^2 + (2+sqrt2)/sqrt(q-1))/u and nu/u
        are non-increasing (checked exactly through squared rational forms), and the ratio is maximal at m = 5.
    The all-q statement is NOT derived from the finite list. It is the paper's monotonicity argument
    (sec_6, proof of Corollary inv13): each of eta_rss/u, (nu^2 + (2+sqrt2)/sqrt(q-1))/u and nu/u is
    non-increasing in q for q >= 32, so theta_2/u is at most its value at m = 5, which is below 489/50.
    The list m = 5..201 is a calibration of that argument, not its proof.
(C) m = 3 calibration of the two-step start lemma (unchanged, run once, imported from p803_steps.py).
JSON main values are exact fractions (strings) or outward intervals [lo, hi]; floats appear only under 'aux'.
"""
import sys, json, os
from fractions import Fraction as Fr
from math import isqrt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import p803_steps as base          # byte-identical copy of c8/checks/p803_steps.py
from p803_steps import sqrt_hi, sqrt_lo

C_FIXED = Fr(489, 50)
K_C_EXPECTED = Fr(323021, 12500)
D13_BOUND = Fr(24405)
ZERO14_BOUND = Fr(169597)
ROUND = 10 ** 12   # denominator used to print outward-rounded decimal intervals


def up(x):
    """outward (upward) rounding of a Fraction to denominator ROUND, returned as exact Fraction."""
    return Fr(-((-x.numerator * ROUND) // x.denominator), ROUND)


def down(x):
    return Fr((x.numerator * ROUND) // x.denominator, ROUND)


def iv(lo, hi):
    assert lo <= hi
    return [str(down(lo)), str(up(hi))]


def fault_requested(argv):
    return os.environ.get('P803_FAULT_C', '') == '1' or '--fault-C1' in argv


def part_A():
    A = base.part_A()
    exact_rows = []
    for m in range(5, 62):
        q = 2 ** m
        x2 = Fr(3 ** m, 4 ** m)
        tau2 = 5 * x2 - Fr(3, q) + Fr(1, q * q)
        nu2 = Fr(2, q - 1) + tau2
        eta2 = Fr(2, q) + Fr(1, q * q - 1)
        cc = (2 + sqrt_hi(Fr(2))) * sqrt_hi(Fr(1, q - 1))
        theta_hi = sqrt_hi(eta2) + sqrt_hi((nu2 + cc) ** 2 + 2 * nu2)
        r_hi = theta_hi / sqrt_lo(x2)
        exact_rows.append({'m': m, 'theta_D2_over_x_upper': str(up(r_hi)),
                           'le_1919_over_240': r_hi <= Fr(1919, 240)})
    consts_ok = (Fr(8, 5) * 10 ** 6 == 1600000) and (1 + Fr(1779, 256) * 1600000 == 11118751) \
        and (Fr(11, 4) + Fr(10, 3) + Fr(153, 80) == Fr(1919, 240))
    rows_ok = all(r['le_1919_over_240'] for r in exact_rows)
    aux = {'rows_float': A['rows']}
    return {'inequalities_all_ok_m5_61': bool(A['all_ok']), 'theta_rows_exact_ok': rows_ok,
            'general_constants': {'D14_coefficient': str(Fr(8, 5) * 10 ** 6),
                                  'zero15_coefficient': str(1 + Fr(1779, 256) * 1600000),
                                  'equalities_ok': consts_ok},
            'constants_c8': A['constants'], 'rows_exact': exact_rows, 'aux': aux,
            'ok': bool(A['all_ok']) and rows_ok and consts_ok}


def terms(m):
    """outward intervals of the three monotone terms and of theta_2/u, u = q^-1/2."""
    q = 2 ** m
    u2 = Fr(1, q)
    u_lo, u_hi = sqrt_lo(u2), sqrt_hi(u2)
    tau2 = Fr(13, q) + Fr(q // 2 - 1, q * q)
    nu2 = Fr(2, q - 1) + tau2
    eta2 = Fr(2, q) + Fr(1, q * q - 1)
    r2_lo, r2_hi = sqrt_lo(Fr(2)), sqrt_hi(Fr(2))
    cc_lo = (2 + r2_lo) * sqrt_lo(Fr(1, q - 1))
    cc_hi = (2 + r2_hi) * sqrt_hi(Fr(1, q - 1))
    t1 = (sqrt_lo(eta2) / u_hi, sqrt_hi(eta2) / u_lo)                 # eta_rss/u
    t2 = ((nu2 + cc_lo) / u_hi, (nu2 + cc_hi) / u_lo)                 # (nu^2+(2+r2)/sqrt(q-1))/u
    t3 = (sqrt_lo(nu2) / u_hi, sqrt_hi(nu2) / u_lo)                   # nu/u
    th_hi = sqrt_hi(eta2) + sqrt_hi((nu2 + cc_hi) ** 2 + 2 * nu2)     # same formula as C8 part B
    th_lo = sqrt_lo(eta2) + sqrt_lo((nu2 + cc_lo) ** 2 + 2 * nu2)
    ratio = (th_lo / u_hi, th_hi / u_lo)
    return t1, t2, t3, ratio


def part_B(C):
    rows, B1, mono = [], True, True
    prev = None
    for m in range(5, 202):
        t1, t2, t3, ratio = terms(m)
        below = ratio[1] < C
        B1 = B1 and below
        # exact squared forms (no square roots): t1^2 = q eta2, t3^2 = q nu2,
        # t2 = sqrt(q nu2^2) + (2+sqrt2) sqrt(q/(q-1)), a sum of two terms each checked separately
        q = 2 ** m
        tau2 = Fr(13, q) + Fr(q // 2 - 1, q * q)
        nu2 = Fr(2, q - 1) + tau2
        eta2 = Fr(2, q) + Fr(1, q * q - 1)
        sq = (q * eta2, q * nu2 * nu2, Fr(q, q - 1), q * nu2)
        if prev is not None and not all(a <= b for a, b in zip(sq, prev)):
            mono = False
        prev = sq
        rows.append({'m': m, 'ratio_interval': iv(*ratio), 'ratio_upper_lt_C': below})
    hi_list = [(r['m'], terms(r['m'])[3][1]) for r in rows[:3]]
    rmax_hi = max(terms(m)[3][1] for m in range(5, 202))
    r5_lo = terms(5)[3][0]
    argmax_is_5 = all(terms(m)[3][1] <= r5_lo for m in range(6, 202)) if mono else False
    C_rule = Fr(int(rmax_hi * 100) + 1, 100)
    B2 = (C_rule == C)
    KC = max(C + Fr(24, 5), Fr(14, 5) + 2 * C / 5 + C * C / 5)
    B3 = (KC == K_C_EXPECTED)
    r2_lo, r2_hi = sqrt_lo(Fr(2)), sqrt_hi(Fr(2))
    D13 = (r2_lo * KC ** 3, r2_hi * KC ** 3)
    Z14 = (1 + Fr(1779, 256) * D13[0], 1 + Fr(1779, 256) * D13[1])
    B4 = (D13[1] < D13_BOUND) and (Z14[1] < ZERO14_BOUND)
    lim = (r2_lo + sqrt_lo((2 + r2_lo) ** 2 + 2 * Fr(31, 2)), r2_hi + sqrt_hi((2 + r2_hi) ** 2 + 2 * Fr(31, 2)))
    ok = B1 and B2 and B3 and B4
    return {
        'C_used': str(C), 'C_fixed_expected': str(C_FIXED),
        'B1_all_ratios_below_C_m5_201': B1, 'B2_C_equals_rounding_rule': B2, 'C_rounding_rule': str(C_rule),
        'B3_K_C_exact': B3, 'K_C': str(KC), 'K_C_expected': str(K_C_EXPECTED),
        'B4_step_constants': B4,
        'sqrt2_interval': iv(r2_lo, r2_hi),
        'D13_coeff_interval': iv(*D13), 'D13_bound': str(D13_BOUND),
        'zero14_coeff_interval': iv(*Z14), 'zero14_bound': str(ZERO14_BOUND),
        'B5_calibration_terms_nonincreasing_m5_201': mono, 'B5_calibration_max_at_m5': argmax_is_5,
        'ratio_rows': rows,
        'limit_q_to_inf_interval': iv(*lim),
        'note': ('All-q argument (paper, sec_6, proof of Corollary inv13): each of eta_rss/u, '
                 '(nu^2+(2+sqrt2)/sqrt(q-1))/u and nu/u is non-increasing in q for q >= 32, so theta_2/u is at '
                 'most its value at m=5, which is below 489/50 (outward rational evaluation). The finite list '
                 'm=5..201 (B1, B5) is a calibration of that argument, not its proof. The q->inf limit (about 7.95) '
                 'is BELOW the finite-q values, so the limit does not bound the ratio; it is reported only for '
                 'information. The C8 note "bounded by the limit" was wrong and is withdrawn.'),
        'aux': {'ratio_float_m5_7': {m: float(v) for m, v in hi_list}, 'K_C_float': float(KC),
                'D13_float': float(D13[1]), 'zero14_float': float(Z14[1]), 'limit_float': float(lim[1])},
        'ok': ok}


def main(argv):
    out = argv[1]
    fault = fault_requested(argv)
    C = Fr(1) if fault else C_FIXED
    A = part_A()
    print('A ok', A['ok'], flush=True)
    B = part_B(C)
    print('B ok', B['ok'], 'C', B['C_used'], 'K_C', B['K_C'], 'B1..B4', B['B1_all_ratios_below_C_m5_201'],
          B['B2_C_equals_rounding_rule'], B['B3_K_C_exact'], B['B4_step_constants'], flush=True)
    Cc = base.part_C()
    C_ok = bool(Cc['ok'])
    Cc = dict(Cc)
    Cc['ok'] = C_ok
    Cc['aux'] = {'max_pi2_inf_float': Cc.pop('max_pi2_inf'), 'one_over_N_float': Cc.pop('one_over_N')}
    Cc['one_over_N'] = str(Fr(1, 64))
    print('C ok', C_ok, flush=True)
    ok = A['ok'] and B['ok'] and C_ok
    res = {'version': 'p803_steps_v2 (C9)', 'fault_injection_C_eq_1': fault,
           'A_ok': A['ok'], 'B_ok': B['ok'], 'C_ok': C_ok, 'all_ok': ok, 'A': A, 'B': B, 'C': Cc}
    with open(out, 'w') as f:
        json.dump(res, f, indent=1, default=str)
        f.write('\n')
    print('P803_ALL_OK' if ok else 'P803_FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
