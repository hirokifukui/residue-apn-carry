"""P3-08: pair-decoupling construction.  For a G direction alpha=(u,v), u not in {0,rho}, the value z0(a) used in
t = D_u p(a) + z0(a)&s depends only on (h(a), h(a+u)), so the conditions for different u-pairs {a, a+u} are
independent.  Choosing (h(a), h(a+u)) per pair so that the condition holds at a (one point per pair) gives, for
s = all-ones, a lift with  #{x : B(x+alpha)-B(x) = (s,t)} >= q/2,  i.e. a G-row element >= 1/(2q).
Also checks the h-independence of z0(a) xor z0(a+u) (the reason both points of a pair cannot in general be taken).
usage: python3 -I a1_gpair.py M   (M in 5, 7)
"""
import sys, os, json
import numpy as np
P = os.path.expanduser('~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher')
sys.path.insert(0, P + '/c1/code')
from codes import mk
from ringlib import GF2m

def main(m):
    q = 1 << m; N = q * q; mask = q - 1
    add, neg, sub, J = mk(m)
    MUL = GF2m(m).MUL
    INV = np.zeros(q, dtype=np.int64)
    for x in range(1, q): INV[x] = int(np.nonzero(MUL[x] == 1)[0][0])
    base = np.load(P + '/c1/data/F_m%d_r3.npy' % m).astype(np.int64)
    X = np.arange(N); A = X & mask; Bh = X >> m
    p = base[np.arange(q)] & mask; hn = base[np.arange(q)] >> m
    d = (base[np.arange(q) | (1 << m)] >> m) ^ hn
    assert np.array_equal(base >> m, hn[A] ^ MUL[d[A], Bh])
    K = d ^ d[0]; rho = [u for u in range(q) if K[u] == 0][1]
    out = {'m': m, 'q': q, 'rho': int(rho), 'cases': []}
    rng = np.random.default_rng(20261010)
    s = mask
    for (u, v, t) in [(2, 0, 0), (3, 5, 7), (int(rng.integers(2, q)) | 2, int(rng.integers(0, q)), int(rng.integers(0, q)))]:
        if u == rho: u ^= 4
        Kinv = int(INV[K[u]])
        h = rng.integers(0, q, q).astype(np.int64)          # background: random lift
        done = set()
        for a in range(q):
            if a in done: continue
            au = a ^ u; done |= {a, au}
            Dp = int(p[au] ^ p[a]); target = t ^ Dp      # need z0(a) == target (s = all ones)
            ok = False
            for hau in range(q):
                b = int(MUL[Kinv, s ^ hau ^ int(h[a]) ^ int(MUL[d[au], v ^ (a & u)])])
                if (int(h[a]) ^ int(MUL[d[a], b])) == target:
                    h[au] = hau; ok = True; break
            assert ok
        F = p[A] | ((h[A] ^ MUL[d[A], Bh]) << m)
        assert len(set(F.tolist())) == N
        Bm = J(F)
        alpha = u | (v << m); delta = s | (t << m)
        D = sub(Bm[add(X, alpha)], Bm)
        cnt = int(np.sum(D == delta))
        rowmax = int(np.bincount(D, minlength=N).max())
        # h-independence of z0(a) xor z0(a+u): compare with a second random background
        def z0(hh, a):
            b = int(MUL[Kinv, s ^ int(hh[a ^ u]) ^ int(hh[a]) ^ int(MUL[d[a ^ u], v ^ (a & u)])])
            return int(hh[a]) ^ int(MUL[d[a], b])
        h2 = rng.integers(0, q, q)
        indep = all((z0(h, a) ^ z0(h, a ^ u)) == (z0(h2, a) ^ z0(h2, a ^ u)) for a in range(q))
        case = {'u': u, 'v': v, 't': t, 's': s, 'count': cnt, 'q_half': q // 2, 'count_ge_q_half': cnt >= q // 2,
                'row_max_count': rowmax, 'pair_xor_h_independent': bool(indep)}
        out['cases'].append(case); print(case, flush=True)
        if m == 5 and len(out['cases']) == 1:
            np.save(P + '/c3/a1/data/F_Gpair.npy', F)
    assert all(c['count_ge_q_half'] and c['pair_xor_h_independent'] for c in out['cases'])
    json.dump(out, open(P + '/c3/a1/results/a1_gpair_m%d.json' % m, 'w'), indent=1)
    print('A1_GPAIR=PASS')

if __name__ == '__main__':
    main(int(sys.argv[1]))
