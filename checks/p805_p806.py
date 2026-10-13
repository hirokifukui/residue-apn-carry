"""p805_p806.py -- C8 (Claude) independent finite checks for P8-05 and P8-06.
Usage: python3 -I -B p805_p806.py OUT.json
P8-05: F_8 = F_2[X]/(X^3+X+1), p = inverse, d = d0, h = [7,5,2,2,2,0,7,2]:
   ell(h) (= A + B^{q/2} with eta = beta = 1), Psi_{L,mu} for (i) all 64 carry-mask keys L(a) = a AND kappa, mu in F_8,
   (ii) the binary linear L with basis images (L(1), L(t), L(t^2)) = (3, 0, 0), mu = 0, (iii) all 8^3 = 512 linear L
   with all 8 mu (count of identically-zero Psi).
P8-06: m = 5, p irrelevant; two admissible d (d0, rho = 1; d = 1 + K0(x/rho), rho = 0b111 of weight 3):
   g_d = chi * r, r = sqrt(eta d) (here eta = 1), chi linear with chi(rho) = 1;
   (a) rank of the quadratic ANF parts of the m output coordinates (= dim of span mod affine functions) == m-1;
   (b) explicit circuit with m-1 AND gates: t = chi(a), v_i = <o_i, r(a)>, outputs O^{-1}(t, t v_1..t v_{m-1}),
       compared with g_d at all 32 points; also XOR counts of the linear parts are recorded.
"""
import sys, json, os, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from grlib import GF, d0_table, dot, popcount


def p805():
    K = GF(3)
    q = K.q
    p = K.inv
    d = d0_table(K)
    h = [7, 5, 2, 2, 2, 0, 7, 2]
    # H = Im r, r = a^2 + a + 1 ; Delta_h(x) = h(a) + h(a+1) for x = r(a)
    H = {}
    for a in range(q):
        x = int(K.mul[a, a]) ^ a ^ 1
        H[x] = h[a] ^ h[a ^ 1]
    A = 0
    B = 0
    for x, D in H.items():
        ix = int(K.inv[x])
        A ^= int(K.mul[K.pw(ix, 3), D])
        B ^= int(K.mul[K.pw(ix, 5), int(K.mul[D, D])])
    ell = A ^ K.pw(B, q // 2)

    def psi(L, mu):
        vals = []
        for c in range(q):
            s = 0
            for a in range(q):
                s ^= int(p[h[a] ^ int(K.mul[d[a], c ^ L[a]]) ^ mu])
            vals.append(s)
        return vals
    carry_zero = []
    for kappa in range(q):
        L = [a & kappa for a in range(q)]
        for mu in range(q):
            if all(v == 0 for v in psi(L, mu)):
                carry_zero.append((kappa, mu))
    Lspec = [((a & 1) * 3) ^ (((a >> 1) & 1) * 0) ^ (((a >> 2) & 1) * 0) for a in range(q)]
    spec_vals = psi(Lspec, 0)
    lin_zero = []
    for imgs in itertools.product(range(q), repeat=3):
        L = [0] * q
        for a in range(q):
            v = 0
            for i in range(3):
                if (a >> i) & 1:
                    v ^= imgs[i]
            L[a] = v
        for mu in range(q):
            if all(v == 0 for v in psi(L, mu)):
                lin_zero.append((imgs, mu))
    res = {'ell_h': ell, 'A': A, 'B': B, 'carry_keys_checked': q * q, 'carry_keys_with_Psi_identically_zero': carry_zero,
           'L_table_spec': Lspec, 'Psi_spec_values': spec_vals, 'spec_identically_zero': all(v == 0 for v in spec_vals),
           'linear_L_mu_checked': q ** 3 * q, 'linear_L_mu_identically_zero_count': len(lin_zero),
           'linear_L_mu_identically_zero_first': lin_zero[:8]}
    ok = ell == 0 and not carry_zero and res['spec_identically_zero']
    return res, ok


def anf(f, m):
    """Moebius transform of a Boolean function given as list of 2^m bits."""
    a = list(f)
    for i in range(m):
        for x in range(1 << m):
            if x >> i & 1:
                a[x] ^= a[x ^ (1 << i)]
    return a


def gf2_rank(rows):
    rows = [r for r in rows]
    rank = 0
    ncol = max((r.bit_length() for r in rows), default=0)
    for c in range(ncol):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i] >> c & 1:
                piv = i
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> c & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def gf2_inv(M, m):
    """M: list of m row ints (row i, bit j = M[i][j]); returns inverse rows."""
    A = [(M[i] | (1 << (m + i))) for i in range(m)]
    for c in range(m):
        piv = next(i for i in range(c, m) if A[i] >> c & 1)
        A[c], A[piv] = A[piv], A[c]
        for i in range(m):
            if i != c and A[i] >> c & 1:
                A[i] ^= A[c]
    return [A[i] >> m for i in range(m)]


def matvec(M, x):
    return sum((popcount(M[i] & x) & 1) << i for i in range(len(M)))


def p806():
    K = GF(5)
    q, m = K.q, K.m
    out = []
    ok = True

    def mk_d(rho):
        ir = int(K.inv[rho])
        tab = []
        for a in range(q):
            x = int(K.mul[a, ir])
            x2 = int(K.mul[x, x])
            tab.append(1 ^ x2 ^ int(K.mul[x2, x2]))
        return tab
    for name, rho in (('d0_rho1', 1), ('d_rho7_wt3', 7)):
        d = mk_d(rho)
        if rho == 1:
            assert d == [int(v) for v in d0_table(K)]
        # eta: Im d = {Tr(eta z) = 1}; here Im d = {Tr = 1}
        assert all(K.tr(v) == 1 for v in d)
        # r = sqrt(d) = d^(q/2)
        r = [K.pw(v, q // 2) for v in d]
        assert all(int(K.mul[x, x]) == v for x, v in zip(r, d))
        assert all(r[a] == r[a ^ rho] for a in range(q))
        jbit = next(i for i in range(m) if rho >> i & 1)
        chi = lambda a: (a >> jbit) & 1
        g = [r[a] if chi(a) else 0 for a in range(q)]
        # (a) quadratic part rank
        quad_rows = []
        degs = []
        for i in range(m):
            coef = anf([(g[a] >> i) & 1 for a in range(q)], m)
            degs.append(max((popcount(x) for x in range(q) if coef[x]), default=-1))
            row = 0
            for idx, x in enumerate(x for x in range(q) if popcount(x) == 2):
                if coef[x]:
                    row |= 1 << idx
            quad_rows.append(row)
        rk = gf2_rank(quad_rows)
        # (b) circuit: O with first row = trace functional, completed by unit rows
        trrow = sum(K.tr(1 << j) << j for j in range(m))
        rows = [trrow]
        for j in range(m):
            cand = rows + [1 << j]
            if gf2_rank(cand) == len(cand):
                rows = cand
            if len(rows) == m:
                break
        O = rows
        Oinv = gf2_inv(O, m)
        and_gates = m - 1
        match = True
        for a in range(q):
            t = chi(a)
            Or = matvec(O, r[a])
            assert Or & 1 == 1  # first coordinate = Tr(r(a)) = 1
            vec = t | sum(((t & ((Or >> i) & 1)) << i) for i in range(1, m))  # m-1 ANDs t AND v_i
            if matvec(Oinv, vec) != g[a]:
                match = False
        xor_Oinv = sum(max(popcount(rw) - 1, 0) for rw in Oinv)
        res = {'d': name, 'rho': rho, 'chi_bit': jbit, 'coord_degrees': degs, 'quadratic_rank_mod_affine': rk,
               'expected_m_minus_1': m - 1, 'circuit_and_gates': and_gates, 'circuit_matches_all_points': match,
               'O_rows': O, 'Oinv_rows': Oinv, 'xor_in_Oinv_naive': xor_Oinv}
        ok = ok and rk == m - 1 and match
        out.append(res)
    return out, ok


def main(o):
    r5, ok5 = p805()
    print('P805', r5['ell_h'], len(r5['carry_keys_with_Psi_identically_zero']), r5['spec_identically_zero'],
          r5['linear_L_mu_identically_zero_count'], flush=True)
    r6, ok6 = p806()
    for x in r6:
        print('P806', x['d'], x['quadratic_rank_mod_affine'], x['circuit_matches_all_points'], flush=True)
    json.dump({'P8-05': r5, 'P8-06': r6, 'ok': ok5 and ok6}, open(o, 'w'), indent=1)
    print('P805_P806_ALL_OK' if ok5 and ok6 else 'P805_P806_FAIL')
    sys.exit(0 if ok5 and ok6 else 1)


if __name__ == '__main__':
    main(sys.argv[1])
