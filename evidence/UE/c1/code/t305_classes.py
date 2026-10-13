"""T3-05 finite companion: class transitions of B = J o F for every nonzero direction.
Checks (C1) against the actual ring subtraction, and C-Z / C-G / C-E (C2, C3, C4) for
several coefficient lifts: natural, h=0 (corrected), seeded random h, and adversarial h
built to attain the C4 bounds (sharpness).  m=5 all lifts; m=7 natural (r=5, r=3).
usage: python3 -I t305_classes.py DATADIR OUTJSON"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ringlib import GR4, GF2m
from codes import mk, selftest

def lift_table(m, p, h, d, MUL):
    q = 1 << m; idx = np.arange(q * q); a = idx & (q - 1); b = idx >> m
    return p[a] | ((h[a] ^ MUL[d[a], b]) << m)

def class_rows(m, F, p, h, d, MUL, check_formula=True):
    q = 1 << m; N = q * q; add, neg, sub, J = mk(m)
    X = np.arange(N); a = X & (q - 1); b = X >> m
    hiF = F >> m
    rows = []
    for alpha in range(1, N):
        u, v = alpha & (q - 1), alpha >> m
        xp = add(X, alpha)
        beta = sub(J(F[xp]), J(F))
        s = beta & (q - 1)
        assert np.array_equal(s, hiF[xp] ^ hiF)
        assert not np.any(beta == 0)
        if check_formula:
            K_u = d[u] ^ d[0]                       # K(u) = d(u)+d(0) (d affine)
            formula = h[a ^ u] ^ h[a] ^ MUL[K_u, b] ^ MUL[d[a ^ u], v ^ (a & u)]
            assert np.array_equal(s, formula), (alpha,)
        z = int(np.count_nonzero(s == 0)); e = int(np.count_nonzero(s == 1))
        cls = 'Z' if u == 0 else ('E' if u == 1 else 'G')
        if cls == 'Z':
            assert z == 0 and e in (0, 2 * q)
        elif cls == 'G':
            cnt = np.bincount(s, minlength=q); assert np.all(cnt == q)
        else:
            sa = s[:q]
            assert np.array_equal(s, np.tile(sa, q))                 # b-independent
            assert np.array_equal(sa[np.arange(q) ^ 1], sa ^ d)       # (C3)
            assert z <= N // 2 and e <= N // 2 and z + e <= N // 2 + q   # (C4)
        rows.append((alpha, cls, z, e))
    return rows

def summarise(rows, q):
    out = {}
    for c in 'ZEG':
        rs = [r for r in rows if r[1] == c]
        mz = max(r[2] for r in rs); me = max(r[3] for r in rs); mb = max(r[2] + r[3] for r in rs)
        out[c] = {'directions': len(rs), 'max_Z_count': mz, 'max_E_count': me, 'max_bad_count': mb,
                  'argmax_bad': [r[0] for r in rs if r[2] + r[3] == mb][:8], 'denominator': q * q}
    return out

def main(datadir, outjson):
    res = {}
    for (m, r) in [(5, 3), (7, 5), (7, 3)]:
        R = GR4(m); K = GF2m(m); q = R.q
        assert selftest(m, R)
        o = json.load(open(os.path.join(datadir, 't303_oracle.json')))
        rec = [x for x in o if x['m'] == m and x['r'] == r][0]
        p, h, d = (np.array(rec[k + '_table']) for k in 'phd')
        F = np.load(os.path.join(datadir, f'F_m{m}_r{r}.npy'))
        assert np.array_equal(F, lift_table(m, p, h, d, K.MUL))
        lifts = {'natural': h}
        if m == 5:
            rng = np.random.default_rng(20261009)
            lifts['h_zero'] = np.zeros(q, dtype=np.int64)
            lifts['h_random_seed20261009'] = rng.integers(0, q, q)
            # adversarial h: for a chosen v0, make s(a)=0 (resp. =rho) on every pair {a,a+1}, a even.
            for tag, target in (('h_adv_Z_v0=5', 0), ('h_adv_E_v0=5', 1)):
                v0 = 5; hh = np.zeros(q, dtype=np.int64)
                for a0 in range(0, q, 2):
                    # s(a0) = h(a0+1)+h(a0)+d(a0+1)(v0 + a0&1)   (u=rho=1, b-independent)
                    hh[a0 + 1] = target ^ K.MUL[d[a0 ^ 1], v0 ^ (a0 & 1)]
                lifts[tag] = hh
        res[f'm{m}_r{r}'] = {}
        for name, hh in lifts.items():
            Fl = lift_table(m, p, hh, d, K.MUL)
            assert len(set(Fl.tolist())) == R.N
            rows = class_rows(m, Fl, p, hh, d, K.MUL)
            res[f'm{m}_r{r}'][name] = summarise(rows, q)
            if name.startswith('h_adv'):
                alpha = 1 | (5 << m)
                row = [x for x in rows if x[0] == alpha][0]
                res[f'm{m}_r{r}'][name]['adversarial_row_alpha_rho+2*sigma(5)'] = {'Z': row[2], 'E': row[3], 'N': R.N}
            print(m, r, name, json.dumps(res[f'm{m}_r{r}'][name]))
    json.dump(res, open(outjson, 'w'), indent=1)
    print('T305=PASS')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
