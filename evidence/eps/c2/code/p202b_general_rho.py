"""P2-02 addendum (C2): the epsilon proof uses only  p APN permutation,  d affine without zeros,  ker K = {0, rho}.
Synthetic check with rho of Hamming weight > 1: keep p from the C1 m=5 table, replace d by d'(a) = c + K'(a)
with K' linear of rank m-1, ker K' = {0, rho'}, c outside Im K'; random h.  Expect DU(J o F) = q.
usage: python3 -I p202b_general_rho.py C1DATADIR OUTJSON
"""
import sys, os, json
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'c1', 'code'))
from codes import mk
from ringlib import GF2m

def main(datadir, outjson):
    m = 5; q = 32; N = q * q; mask = q - 1
    add, neg, sub, J = mk(m); MUL = GF2m(m).MUL
    base = np.load(os.path.join(datadir, 'F_m5_r3.npy')).astype(np.int64)
    p = base[np.arange(q)] & mask
    X = np.arange(N); A = X & mask; Bh = X >> m
    rng = np.random.default_rng(7)
    res = []
    for rho in (0b00111, 0b10101, 0b11111):
        # K': linear map F2^5 -> F2^5 with kernel {0,rho}: compose projection along rho with a random injection
        while True:
            Mx = rng.integers(0, 2, (m, m))
            img = [int(sum(int(Mx[i, j]) << i for i in range(m))) for j in range(m)]
            def Kf(x):
                r = 0
                for j in range(m):
                    if (x >> j) & 1: r ^= img[j]
                return r
            Kt = np.array([Kf(x) for x in range(q)])
            if sorted(np.nonzero(Kt == 0)[0].tolist()) == [0, rho]: break
        Im = set(Kt.tolist()); c = next(x for x in range(q) if x not in Im)
        d = c ^ Kt
        assert np.all(d != 0)
        h = rng.integers(0, q, q)
        F = p[A] | ((h[A] ^ MUL[d[A], Bh]) << m); Bm = J(F)
        assert len(set(Bm.tolist())) == N
        best = 0; cls_best = {}
        for alpha in range(1, N):
            u = alpha & mask
            mx = int(np.bincount(sub(Bm[add(X, alpha)], Bm), minlength=N).max())
            cls = 'Z' if u == 0 else ('E' if u == rho else 'G')
            cls_best[cls] = max(cls_best.get(cls, 0), mx); best = max(best, mx)
        rec = {'rho': rho, 'rho_weight': bin(rho).count('1'), 'DU_B': best, 'max_by_class': cls_best}
        assert best == q, rec
        res.append(rec); print(json.dumps(rec), flush=True)
    json.dump(res, open(outjson, 'w'), indent=1)
    print('P202B_GENERAL_RHO=PASS')

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
