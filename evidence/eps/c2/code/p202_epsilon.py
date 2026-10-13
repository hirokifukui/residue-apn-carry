"""P2-02 calibration (C2, Claude 2026-10-09): DU(B) = q for every coefficient lift h, B = J o F.
F(a,b) = (p(a), h(a) + d(a) b).  We extract p, h, d from a C1 table, then rebuild F_h for
h = natural, h = 0, adversarial G table (if given), and random h (seeds), and check
  (1) the closed formulas  s = h(a+u)+h(a)+K(u)b+d(a+u)(v+a*u),  t = D_u p(a) + z0*s  on every input/direction sample,
  (2) per-class maxima  G <= q, Z <= 2q/2^wt(s), E <= q,  and overall max = q,
  (3) the explicit witness alpha=(0, eta/d0), beta=(eta, 0) reaches exactly q.
usage: python3 -I p202_epsilon.py C1DATADIR OUTJSON m NAME [NAME ...]
"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'c1', 'code'))
from codes import mk
from ringlib import GF2m

def main(datadir, outjson, m, names):
    q = 1 << m; N = q * q; mask = q - 1
    add, neg, sub, J = mk(m)
    Fq = GF2m(m); MUL = Fq.MUL
    INV = np.zeros(q, dtype=np.int64)
    for x in range(1, q):
        INV[x] = int(np.nonzero(MUL[x] == 1)[0][0])
    out = {'m': m, 'q': q, 'N': N, 'variants': {}}
    X = np.arange(N); A = X & mask; Bh = X >> m
    rng = np.random.default_rng(20261009)
    tables = {}
    for name in names:
        tables[name] = np.load(os.path.join(datadir, name + '.npy')).astype(np.int64)
    base = tables[names[0]]
    p = base[np.arange(q)] & mask
    for name, F in tables.items():
        assert np.array_equal(F[X] & mask, p[A]), 'lo digit depends on b'
    h_nat = base[np.arange(q)] >> m
    d = (base[np.arange(q) | (1 << m)] >> m) ^ h_nat
    assert np.array_equal(base >> m, h_nat[A] ^ MUL[d[A], Bh]), 'hi digit not h(a)+d(a)b'
    assert np.all(d != 0), 'd has a zero'
    K = d ^ d[0]
    ker = [u for u in range(q) if K[u] == 0]
    assert len(ker) == 2
    rho = ker[1]
    # K linear
    for u in range(q):
        for v in (1, 3, 7, rho):
            assert K[u ^ v] == K[u] ^ K[v]
    out['rho'] = rho; out['rho_weight'] = bin(rho).count('1')
    out['p_is_permutation'] = bool(len(set(p.tolist())) == q)
    variants = {'natural': h_nat, 'h0': np.zeros(q, dtype=np.int64)}
    for name in names[1:]:
        hh = tables[name][np.arange(q)] >> m
        assert np.array_equal(tables[name] >> m, hh[A] ^ MUL[d[A], Bh]), name
        variants[name] = hh
    for s in range(3):
        variants['random%d' % s] = rng.integers(0, q, q)
    popc = np.array([bin(i).count('1') for i in range(q)])
    for vname, h in variants.items():
        F = p[A] | ((h[A] ^ MUL[d[A], Bh]) << m)
        Bm = J(F)
        assert len(set(Bm.tolist())) == N
        best = {'G': 0, 'Z': 0, 'E': 0}; zviol = 0; formula_ok = True
        nchk = 0
        for alpha in range(1, N):
            u, v = alpha & mask, alpha >> m
            Y = sub(Bm[add(X, alpha)], Bm)
            c = np.bincount(Y, minlength=N)
            cls = 'Z' if u == 0 else ('E' if u == rho else 'G')
            mx = int(c.max())
            best[cls] = max(best[cls], mx)
            if cls == 'Z':
                sv = Y & mask
                # bound 2q/2^wt(s) for every beta
                lim = 2 * q // (1 << popc[np.arange(N) & mask])
                if np.any(c > lim): zviol += 1
            if alpha % 97 == 1 or alpha < 40:
                nchk += 1
                a, b = A, Bh
                ap = a ^ u
                s = h[ap] ^ h[a] ^ MUL[K[u], b] ^ MUL[d[ap], v ^ (a & u)]
                z0 = h[a] ^ MUL[d[a], b]
                t = p[ap] ^ p[a] ^ (z0 & s)
                if not np.array_equal(Y, s | (t << m)): formula_ok = False
        # witness
        eta = 1; d0 = int(d[0]); v = int(MUL[eta, INV[d0]]); alpha = v << m; beta = eta
        cw = int(np.sum(sub(Bm[add(X, alpha)], Bm) == beta))
        rec = {'DU_B': max(best.values()), 'max_by_class': best, 'Z_bound_violations': zviol,
               'formula_checked_directions': nchk, 'formula_ok': formula_ok,
               'witness_alpha': alpha, 'witness_beta': beta, 'witness_count': cw}
        assert rec['DU_B'] == q and best['G'] <= q and best['E'] <= q and zviol == 0 and formula_ok and cw == q, rec
        out['variants'][vname] = rec
        print(vname, json.dumps(rec), flush=True)
    json.dump(out, open(outjson, 'w'), indent=1)
    print('P202_EPSILON=PASS')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4:])
