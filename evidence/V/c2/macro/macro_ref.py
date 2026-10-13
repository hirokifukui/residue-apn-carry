"""P2-07: reference encrypt/decrypt of the macro (superbox) construction CANDIDATE_P2_SUPERBOX (C2, Claude 2026-10-09).

NOT the C1 interleaved candidate H = M o B^w (CANDIDATE_P1*).  Research toy in the INDEPENDENT-KEY MODEL only
(no key schedule; every key word below is an independent input).

  S_t(x; k_1..k_t) = F( B( ... B( B(x) + k_1 ) + k_2 ... ) + k_t )      one word x in R = GR(4,m)
  E(x)             = S_t^(2)( M . S_t^(1)(x + k_0) + L )                  x in R^w, wordwise S-layers
  keys: k_0 in R^w (whitening, optional, counted separately), K1[j][i], K2[j][i] (j=word, i=1..t), L in R^w.

Arithmetic is REUSED from C1 (no re-implementation): ring add/neg/sub/J from c1/code/codes.py (mk), ring
multiplication from c1/code/ringlib.py (GR4.mul, GR4.inv_unit), field F_q from ringlib.GF2m, F from c1/data/F_*.npy.
Inverse is derived from the formula (see c2/notes/MACRO_IMPL_P2.md):
  F^{-1}(y0,y1): a = p^{-1}(y0), b = (y1 xor h(a)) * d(a)^{-1} in F_q ;  B^{-1} = F^{-1} o J ;
  M^{-1} by Gauss-Jordan over R (pivots must be units) ;  keys are subtracted in R.
The table argsort(F) is used ONLY as a cross-check of the formula inverse (assert).
"""
import os, sys, json, hashlib
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
C1 = os.path.normpath(os.path.join(HERE, '..', '..', 'c1'))
sys.path.insert(0, os.path.join(C1, 'code'))
from codes import mk                 # noqa: E402
from ringlib import GR4, GF2m        # noqa: E402

F_FILES = {(5, 3): 'F_m5_r3.npy', (7, 3): 'F_m7_r3.npy', (7, 5): 'F_m7_r5.npy'}
MODULUS_TEXT = {5: 't^5+t^2+1', 7: 't^7+t+1'}


def sha_table(a):
    return hashlib.sha256(np.asarray(a).astype(np.int64).tobytes()).hexdigest()


class Ring:
    """thin wrapper: code-level ops (all borrowed from C1)."""
    def __init__(self, m):
        self.m = m; self.q = 1 << m; self.N = self.q * self.q; self.mask = self.q - 1
        self.add, self.neg, self.sub, self.J = mk(m)
        self.R = GR4(m); self.K = GF2m(m)
        self._mt = {}

    def mulc(self, c):
        """table x -> c*x on codes, via ringlib GR4.mul."""
        c = int(c)
        if c not in self._mt:
            self._mt[c] = self.R.encode(self.R.mul(self.R.all, self.R.decode(np.array([c]))[0]))
        return self._mt[c]

    def mul(self, a, b):
        return int(self.mulc(a)[int(b)])

    def is_unit(self, c):
        return (int(c) & self.mask) != 0

    def inv(self, c):
        return int(self.R.encode(self.R.inv_unit(self.R.decode(np.array([int(c)]))[0])[None])[0])

    def mat_inv(self, M):
        """Gauss-Jordan over R; refuses if no unit pivot exists."""
        w = len(M)
        A = [[int(v) for v in row] + [1 if i == j else 0 for j in range(w)] for i, row in enumerate(M)]
        for c in range(w):
            p = next((r for r in range(c, w) if self.is_unit(A[r][c])), None)
            if p is None:
                raise ValueError('matrix not invertible over R (no unit pivot)')
            A[c], A[p] = A[p], A[c]
            iv = self.inv(A[c][c]); A[c] = [self.mul(iv, v) for v in A[c]]
            for r in range(w):
                if r != c and A[r][c]:
                    f = A[r][c]; A[r] = [self.sub(A[r][k], self.mul(f, A[c][k])) for k in range(2 * w)]
        return [row[w:] for row in A]

    def mat_apply(self, M, xs):
        """xs: list of w code arrays -> M . xs over R."""
        w = len(M); out = []
        for i in range(w):
            acc = self.mulc(M[i][0])[xs[0]]
            for j in range(1, w):
                acc = self.add(acc, self.mulc(M[i][j])[xs[j]])
            out.append(acc)
        return out


class SBox:
    """F, its (p,h,d) decomposition read off the C1 table, formula inverse, B = J o F, B^{-1} = F^{-1} o J."""
    def __init__(self, ring, ffile):
        self.rg = rg = ring; m, q, N, mask = ring.m, ring.q, ring.N, ring.mask
        self.F = np.load(ffile).astype(np.int64); assert self.F.shape == (N,)
        self.F_sha256 = sha_table(self.F)
        a = np.arange(q)
        self.p = self.F[a] & mask                     # digit-0 output at b = 0
        self.h = self.F[a] >> m                       # digit-1 output at b = 0
        self.d = (self.F[a | (1 << m)] >> m) ^ self.h  # coefficient of b (b = 1 in F_q)
        # verify the table IS (p(a), h(a) xor d(a)*b) for every (a,b)
        X = np.arange(N); aa = X & mask; bb = X >> m
        pred = self.p[aa] | ((self.h[aa] ^ rg.K.MUL[self.d[aa], bb]) << m)
        assert np.array_equal(pred, self.F), 'F table is not of the form (p(a), h(a)+d(a)b)'
        assert len(np.unique(self.p)) == q and np.all(self.d != 0)
        self.pinv = np.argsort(self.p)
        self.dinv = np.array([rg.K.pow(int(v), q - 2) for v in self.d], dtype=np.int64)
        assert np.all(rg.K.MUL[self.d, self.dinv] == 1)
        self.B = rg.J(self.F)

    def Finv(self, y):
        y = np.asarray(y, dtype=np.int64); rg = self.rg
        a = self.pinv[y & rg.mask]
        b = self.rg.K.MUL[(y >> rg.m) ^ self.h[a], self.dinv[a]]
        return a | (b << rg.m)

    def Binv(self, y):
        return self.Finv(self.rg.J(np.asarray(y, dtype=np.int64)))


class Macro:
    def __init__(self, m, r, w, t, M, whitening=True, datadir=os.path.join(C1, 'data')):
        self.rg = Ring(m); self.sb = SBox(self.rg, os.path.join(datadir, F_FILES[(m, r)]))
        self.m, self.r, self.w, self.t, self.whitening = m, r, w, t, whitening
        self.M = [[int(v) for v in row] for row in M]; self.Minv = self.rg.mat_inv(self.M)
        I = [[1 if i == j else 0 for j in range(w)] for i in range(w)]
        prod = [[0] * w for _ in range(w)]
        for i in range(w):
            for j in range(w):
                acc = 0
                for k in range(w):
                    acc = self.rg.add(acc, self.rg.mul(self.M[i][k], self.Minv[k][j]))
                prod[i][j] = int(acc)
        assert prod == I, 'M * M^-1 != I over R'

    # ---- keys ---------------------------------------------------------------
    def random_keys(self, rng):
        N, w, t = self.rg.N, self.w, self.t
        g = lambda *s: rng.integers(0, N, s).tolist()
        k = {'K1': g(w, t), 'L': g(w), 'K2': g(w, t)}
        k['k0'] = g(w) if self.whitening else [0] * w
        return k

    def key_positions(self):
        pos = []
        if self.whitening:
            pos += [('k0', j) for j in range(self.w)]
        pos += [('K1', j, i) for j in range(self.w) for i in range(self.t)]
        pos += [('L', j) for j in range(self.w)]
        pos += [('K2', j, i) for j in range(self.w) for i in range(self.t)]
        return pos

    # ---- one word -----------------------------------------------------------
    def S(self, x, ks):
        add, B, F = self.rg.add, self.sb.B, self.sb.F
        for k in ks:
            x = add(B[x], k)
        return F[x]

    def Sinv(self, y, ks):
        z = self.sb.Finv(y)
        for k in reversed(ks):
            z = self.sb.Binv(self.rg.sub(z, k))
        return z

    # ---- block --------------------------------------------------------------
    def enc(self, xs, keys):
        rg = self.rg
        xs = [np.asarray(x, dtype=np.int64) for x in xs]
        u = [self.S(rg.add(xs[j], keys['k0'][j]), keys['K1'][j]) for j in range(self.w)]
        v = rg.mat_apply(self.M, u)
        v = [rg.add(v[j], keys['L'][j]) for j in range(self.w)]
        return [self.S(v[j], keys['K2'][j]) for j in range(self.w)]

    def dec(self, ys, keys):
        rg = self.rg
        ys = [np.asarray(y, dtype=np.int64) for y in ys]
        v = [rg.sub(self.Sinv(ys[j], keys['K2'][j]), keys['L'][j]) for j in range(self.w)]
        u = rg.mat_apply(self.Minv, v)
        return [rg.sub(self.Sinv(u[j], keys['K1'][j]), keys['k0'][j]) for j in range(self.w)]

    def counts(self):
        w, t = self.w, self.t
        return {'F_evaluations_total (incl. inside B)': 2 * w * (t + 1), 'B_evaluations': 2 * w * t,
                'F_outside_B': 2 * w, 'J': 2 * w * t, 'M_applications': 1,
                'M_const_mults': w * w, 'M_additions': w * (w - 1),
                'internal_key_words (K1,K2)': 2 * w * t, 'interlayer_key_words (L)': w,
                'whitening_key_words (k0)': w if self.whitening else 0,
                'total_key_words': 2 * w * t + w + (w if self.whitening else 0),
                'key_additions': 2 * w * t + w + (w if self.whitening else 0)}


def mixers(m):
    """two-word: MDS_alt / M2 from c1/spec/mixer2.json (m=5 only for M2); four-word: Cauchy as in t312b."""
    K = GF2m(m); q = K.q
    xs, ys = [1, 2, 3, 4], [5, 6, 7, 8]
    cauchy = [[K.pow(x ^ y, q - 2) for y in ys] for x in xs]
    out = {'MDS_alt': [[1, 1], [1, 2]], 'Cauchy4': cauchy}
    if m == 5:
        mix = json.load(open(os.path.join(C1, 'spec', 'mixer2.json')))['mixers']
        assert mix['MDS_alt_[[1,1],[1,t]]']['matrix_codes'] == [[1, 1], [1, 2]]
        out['M2'] = mix['M2_paper2_type']['matrix_codes']
    return out
