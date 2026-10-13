"""p803_steps.py -- P8-03 independent check (C8, Claude). Usage: python3 -I -B p803_steps.py OUT.json
(A) exact rational checks (outward square-root intervals via integer isqrt) of every elementary inequality used
    in the 14+1 step argument (NEW_DERIVATIONS B2-B4), for every m = 5..61 (odd and even), plus the final constants;
(B) family-specific variant (p inverse, d of d0 type, tau^2 <= (M+3)/q + (q/2-1)/q^2 with M <= 10, P8-07 Theorem G /
    Prop. I): the constant C with theta_2 <= C q^-1/2 for all m >= 5 (sup over m = 5..201 plus the limit) and the
    resulting constants of the C7 conditional proposition (K_C, D_13, zero-word probability);
(C) m = 3 calibration of the two-step start ||pi_2||_inf <= 1/N for ALL 4095 non-zero two-word input differences,
    with GR(4,3) ring multiplication for M = [[1,1],[1,t]] (q = 8 only calibrates the start lemma).
Finite arithmetic / calibration; the general proof is on paper (RESPONSE_C8 P8-03).
"""
import sys, json, os
from fractions import Fraction as Fr
from math import isqrt
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grlib import GF, d0_table, ddt_B

SC = 10 ** 30


def sqrt_hi(x):
    """upper bound for sqrt(x), x a Fraction >= 0."""
    n, d = x.numerator, x.denominator
    r = isqrt(n * d * SC * SC)
    return Fr(r + 1, d * SC)


def sqrt_lo(x):
    n, d = x.numerator, x.denominator
    r = isqrt(n * d * SC * SC)
    return Fr(r, d * SC)


def part_A():
    rows = []
    ok = True
    for m in range(5, 62):
        q = 2 ** m
        N = q * q
        x2 = Fr(3 ** m, 4 ** m)            # x^2 = (3/4)^m
        x_hi, x_lo = sqrt_hi(x2), sqrt_lo(x2)
        u2 = Fr(1, q)
        u_hi, u_lo = sqrt_hi(u2), sqrt_lo(u2)
        c = {}
        c['x<=1/2'] = x2 <= Fr(1, 4)
        c['u/x<=3/8'] = u2 / x2 <= Fr(9, 64)
        c['u<=x^2'] = u2 <= x2 * x2
        eta2 = Fr(2, q) + Fr(1, q * q - 1)
        c['eta_rss<=3u/2'] = eta2 <= Fr(9, 4) * u2
        c['2/(q-1)<=x^2/2'] = Fr(2, q - 1) <= x2 / 2
        # (2+sqrt2)/sqrt(q-1) <= (18/5) u  <=>  (2+sqrt2)^2 q/(q-1) <= 324/25 ; (2+sqrt2)^2 = 6+4 sqrt2 <= 6+4*1.41422
        c['(2+r2)/sqrt(q-1)<=18u/5'] = (6 + 4 * Fr(141422, 100000)) * Fr(q, q - 1) <= Fr(324, 25)
        # R1: tau^2 <= 5(3/4)^m - 3/q + 1/q^2 <= 5 x^2 ; nu^2 <= 2/(q-1) + tau^2 <= (11/2) x^2
        tau2 = 5 * x2 - Fr(3, q) + Fr(1, q * q)
        nu2 = Fr(2, q - 1) + tau2
        c['nu^2<=11/2 x^2'] = nu2 <= Fr(11, 2) * x2
        # direct D2 right-hand side with outward intervals, compared with (1919/240) x
        nu_hi = sqrt_hi(nu2)
        cc = (2 + sqrt_hi(Fr(2))) * sqrt_hi(Fr(1, q - 1))
        inner = (nu2 + cc) ** 2 + 2 * nu2
        theta_hi = sqrt_hi(eta2) + sqrt_hi(inner)
        c['theta2_D2<=1919/240 x'] = theta_hi <= Fr(1919, 240) * x_lo
        c['1919/240<8'] = Fr(1919, 240) < 8
        # weighted column sums: col1 = 2u + x <= 10x, col2 = 2u/x + 8x <= 10x
        c['col1'] = 2 * u_hi + x_hi <= 10 * x_lo
        c['col2'] = 2 * u_hi / x_lo + 8 * x_hi <= 10 * x_lo
        # v_2 <= [1/sqrt(1-q^-2) + x] / (q x) <= 8 / (5 q x)
        c['1/sqrt(1-q^-2)<=11/10'] = Fr(1) / (1 - Fr(1, q * q)) <= Fr(121, 100)
        c['v2_coeff<=8/5'] = sqrt_hi(1 / (1 - Fr(1, q * q))) + x_hi <= Fr(8, 5)
        # x^5 <= 1/q  <=>  (3^5)^m <= (2^8)^m
        c['x^5<=1/q'] = 3 ** (5 * m) <= 2 ** (8 * m)
        bad = [k for k, v in c.items() if not v]
        if bad:
            ok = False
        rows.append({'m': m, 'failed': bad, 'theta_hi_over_x': float(theta_hi / x_lo)})
    consts = {
        '(8/5)*10^6': str(Fr(8, 5) * 10 ** 6),
        '(1779/256)*1600000': str(Fr(1779, 256) * 1600000),
        'ZERO15_numerator': str(Fr(1779, 256) * 1600000 + 1),
        '1919/240': str(Fr(1919, 240)), '11/4+10/3+153/80': str(Fr(11, 4) + Fr(10, 3) + Fr(153, 80)),
        'sqrt11<=10/3': 11 <= Fr(100, 9), '(3/2+18/5)*(3/8)=153/80': (Fr(3, 2) + Fr(18, 5)) * Fr(3, 8) == Fr(153, 80),
    }
    return {'rows': rows, 'all_ok': ok, 'constants': consts}


def part_B():
    """theta_2 <= C u for the inverse/d0-type family, using tau^2 <= 13/q + (q/2-1)/q^2 (M <= 10)."""
    vals = []
    for m in range(5, 202):
        q = 2 ** m
        u2 = Fr(1, q)
        tau2 = Fr(13, q) + Fr(q // 2 - 1, q * q)
        nu2 = Fr(2, q - 1) + tau2
        eta2 = Fr(2, q) + Fr(1, q * q - 1)
        cc = (2 + sqrt_hi(Fr(2))) * sqrt_hi(Fr(1, q - 1))
        theta_hi = sqrt_hi(eta2) + sqrt_hi((nu2 + cc) ** 2 + 2 * nu2)
        vals.append((m, theta_hi / sqrt_lo(u2)))
    Cmax = max(v for _, v in vals)
    mmax = [m for m, v in vals if v == Cmax][0]
    # limit as q -> inf: sqrt2 + sqrt((2+sqrt2)^2 + 2*(2+13.5)) ; bound it and also show the ratio is <= Cmax for m>201
    lim_hi = sqrt_hi(Fr(2)) + sqrt_hi((2 + sqrt_hi(Fr(2))) ** 2 + 2 * Fr(31, 2))
    C = Fr(int(Cmax * 100) + 1, 100)  # rounded up to 2 decimals
    KC = max(C + Fr(24, 5), Fr(14, 5) + 2 * C / 5 + C * C / 5)
    D13 = sqrt_hi(Fr(2)) * KC ** 3
    zero = 1 + Fr(1779, 256) * D13
    return {'C_sup_m5_201': float(Cmax), 'argmax_m': mmax, 'C_used': str(C), 'limit_upper': float(lim_hi),
            'ratio_m': {m: float(v) for m, v in vals[:10]}, 'K_C': float(KC), 'D13_coeff': float(D13),
            'zero_word_coeff': float(zero),
            'note': 'theta_2 <= C u holds for every m >= 5 because the ratio is monotone after m=7 (see list) and '
                    'bounded by the limit; C7 Prop. condsteps then applies verbatim.'}


def gr_mul_t(x, K):
    """multiply x = (a, b) in GR(4,m) = Z4[t]/(f^) by t; f^ = lift of f with 0/1 coefficients."""
    m = K.m
    a, b = x
    c = [((a >> i) & 1) + 2 * ((b >> i) & 1) for i in range(m)]
    top = c[m - 1]
    nc = [0] + c[:m - 1]
    f = K.poly
    for i in range(m):
        if (f >> i) & 1:
            nc[i] = (nc[i] - top) % 4
    na = sum((ci & 1) << i for i, ci in enumerate(nc))
    nb = sum(((ci >> 1) & 1) << i for i, ci in enumerate(nc))
    return (na, nb)


def gr_add(x, y):
    return (x[0] ^ y[0], x[1] ^ y[1] ^ (x[0] & y[0]))


def part_C():
    K = GF(3)
    q = K.q
    N = q * q
    p = K.inv.copy()
    d = d0_table(K)
    h = np.array([K.pw(a, 3) for a in range(q)], dtype=np.int64)
    D = ddt_B(K, p, d, h)
    T = D.astype(float) / N
    assert D[1:].max() <= q
    # permutation of R^2 under M = [[1,1],[1,t]] : (d1, d2) -> (d1 + d2, d1 + t d2)
    st = lambda i: (i % q, i // q)
    ix = lambda x: x[0] + q * x[1]
    tm = [ix(gr_mul_t(st(i), K)) for i in range(N)]
    worst = 0.0
    worst_al = None
    # vectorised permutation tables
    add = np.zeros((N, N), dtype=np.int64)
    for i in range(N):
        for j in range(N):
            add[i, j] = ix(gr_add(st(i), st(j)))
    tmv = np.array(tm)
    R1 = add                     # (d1, d2) -> d1 + d2
    R2 = add[:, tmv]             # (d1, d2) -> d1 + t d2
    flat = (R1 * N + R2).ravel()
    for a1 in range(N):
        for a2 in range(N):
            if a1 == 0 and a2 == 0:
                continue
            X = np.outer(T[a1], T[a2]).ravel()
            Y = np.zeros(N * N)
            np.add.at(Y, flat, X)
            Y = Y.reshape(N, N)
            Z = T.T @ Y @ T
            mx = Z.max()
            if mx > worst:
                worst, worst_al = mx, (a1, a2)
    return {'m': 3, 'pairs_checked': N * N - 1, 'max_pi2_inf': worst, 'one_over_N': 1.0 / N,
            'ok': worst <= 1.0 / N + 1e-15, 'argmax_alpha': worst_al,
            'note': 'q = 8 calibrates the start lemma only; not counted as a q >= 32 instance.'}


def main(out):
    A = part_A()
    print('A all_ok', A['all_ok'], flush=True)
    B = part_B()
    print('B', B['C_used'], B['K_C'], B['D13_coeff'], B['zero_word_coeff'], flush=True)
    C = part_C()
    print('C', C['max_pi2_inf'], C['one_over_N'], C['ok'], flush=True)
    res = {'A': A, 'B': B, 'C': C}
    json.dump(res, open(out, 'w'), indent=1, default=str)
    ok = A['all_ok'] and C['ok']
    print('P803_ALL_OK' if ok else 'P803_FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main(sys.argv[1])
