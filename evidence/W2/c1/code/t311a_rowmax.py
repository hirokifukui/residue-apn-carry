"""T3-11 input: row maxima mu_C = max_{alpha in C, beta} T_B(alpha,beta) (as counts, i.e. times N).
Proved caps (any lift, k=2): mu_Z <= q (i.e. 1/q), mu_E <= 2q (2/q), mu_G <= min(q, 2^{wt(s)+1}) (lift-dependent).
Computes: natural lifts m=5 (r=3), m=7 (r=5,3) all rows; and an ADVERSARIAL coefficient lift at m=5 that makes one
G row concentrate: for alpha=(u,v)=(2,0) and target residue s = all-ones, choose h pairwise so that the B-difference
upper digit is constant -> T_B(alpha,beta*) = q/N = 1/q.
usage: python3 -I t311a_rowmax.py DATADIR OUTJSON"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from codes import mk
from ringlib import GF2m
from t305_classes import lift_table

def rowmax(m, F):
    q = 1 << m; N = q * q; add, neg, sub, J = mk(m); B = J(F); X = np.arange(N)
    mu = {'Z': 0, 'E': 0, 'G': 0}; arg = {}
    hist = {}
    for a in range(1, N):
        c = 'Z' if (a & (q - 1)) == 0 else ('E' if (a & (q - 1)) == 1 else 'G')
        r = np.bincount(sub(B[add(X, a)], B), minlength=N); mx = int(r.max())
        if c == 'G': hist[mx] = hist.get(mx, 0) + 1
        if mx > mu[c]: mu[c] = mx; arg[c] = (a, int(r.argmax()))
    return mu, arg, hist

def adversarial(m, p, d, K, u=2, v=0, w=0):
    """solve for h so that, for alpha=(u,v), every a gives the same B-difference (s=all ones, upper=w)."""
    q = 1 << m; s = q - 1
    Ku = d[u] ^ d[0]; Kinv = [x for x in range(1, q) if K.MUL[Ku, x] == 1][0]
    D = np.array([p[a ^ u] ^ p[a] for a in range(q)])
    h = np.zeros(q, dtype=np.int64)
    # B-difference for base (a,b): lower s_ab = h(a^u)^h(a)^Ku*b^d(a^u)(v^(a&u)); upper = D(a) ^ (z0 & s_ab),
    # z0 = h(a)^d(a)b.  Want s_ab = s and upper = w:  need z0 = D(a)^w (since s = all ones, z0&s = z0).
    # For pair {a, a^u}: unknowns h(a), h(a^u). From z0 condition, b = d(a)^{-1}(D(a)^w^h(a)); plug into s-condition.
    inv = {x: [y for y in range(1, q) if K.MUL[x, y] == 1][0] for x in range(1, q)}
    done = set(); unsolved = []
    for a in range(q):
        if a in done: continue
        a2 = a ^ u; done |= {a, a2}
        found = False
        for ha in range(q):
            for ha2 in range(q):
                ok = True
                for (x, hx, hy) in ((a, ha, ha2), (a2, ha2, ha)):
                    b = K.MUL[inv[d[x]], D[x] ^ w ^ hx]
                    sval = hy ^ hx ^ K.MUL[Ku, b] ^ K.MUL[d[x ^ u], v ^ (x & u)]
                    if sval != s: ok = False; break
                if ok: h[a], h[a2] = ha, ha2; found = True; break
            if found: break
        if not found:
            unsolved.append(a)
            # satisfy the equation of base a only: h(a)=0, solve for h(a^u) (coefficient of h(a^u) is 1 in the s-condition)
            b = K.MUL[inv[d[a]], D[a] ^ w]
            h[a] = 0; h[a2] = s ^ K.MUL[Ku, b] ^ K.MUL[d[a2], v ^ (a & u)]
    return h, unsolved

def main(datadir, outjson):
    o = json.load(open(os.path.join(datadir, 't303_oracle.json'))); res = {}
    for (m, r) in [(5, 3), (7, 5), (7, 3)]:
        rec = [x for x in o if x['m'] == m and x['r'] == r][0]
        F = np.load(os.path.join(datadir, f'F_m{m}_r{r}.npy'))
        mu, arg, hist = rowmax(m, F); q = 1 << m
        assert mu['Z'] <= q and mu['E'] <= 2 * q and mu['G'] <= q
        res[f'm{m}_r{r}_natural'] = {'mu_counts': mu, 'argmax': arg, 'G_row_max_histogram': hist, 'N': q * q}
        print(m, r, mu, arg)
    rec = [x for x in o if x['m'] == 5][0]; p, h0, d = (np.array(rec[k + '_table']) for k in 'phd'); K = GF2m(5)
    hadv, unsolved = adversarial(5, p, d, K)
    Fadv = lift_table(5, p, hadv, d, K.MUL); assert len(set(Fadv.tolist())) == 1024
    np.save(os.path.join(datadir, 'F_m5_r3_adversarialG.npy'), Fadv)
    mu, arg, hist = rowmax(5, Fadv)
    res['m5_r3_adversarial_G_lift'] = {'construction': 'alpha=(u,v)=(2,0), target residue all-ones, upper 0', 'h_table': hadv.tolist(), 'unsolvable_pairs_left_h0': unsolved,
                                       'mu_counts': mu, 'argmax': arg, 'N': 1024}
    assert mu['G'] >= 16
    print('adversarial', mu, arg)
    json.dump(res, open(outjson, 'w'), indent=1, default=int); print('T311A=PASS')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
