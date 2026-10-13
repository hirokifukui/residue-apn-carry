"""C5 lane A1 (P5-04/05/06), Claude 2026-10-11.  Independent arithmetic: imports NO c1-c4 code.

Representation (same convention as the project, re-derived here):
  R = GR(4,m) = Z4[t]/(f), f = basic lift with 0/1 coefficients (m5: 1+t^2+t^5, m7: 1+t+t^7).
  An element with Z4-digit vector c_i = a_i + 2 b_i (a_i,b_i in {0,1}) has code x = a | (b << m)
  (a = lo = reduction mod 2, b = hi).  F_q = F_2[t]/(f mod 2), elements as m-bit ints.
  Ring addition on codes: (a,b)+(a',b') = (a^a', b^b'^(a&a')),  -(a,b) = (a, a^b).
  PD S-box: F(a,b) = (p(a), h(a) xor d(a)*b) (field product), B = J o F, J(a,b) = (b,a).
"""
import numpy as np

MOD = {5: (1, 0, 1, 0, 0, 1), 7: (1, 1, 0, 0, 0, 0, 0, 1)}   # c_0..c_m


def modbits(m):
    return sum(c << i for i, c in enumerate(MOD[m]))


class GF:
    def __init__(self, m):
        self.m = m; q = self.q = 1 << m; mod = modbits(m)
        T = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                x, y, z = a, b, 0
                while y:
                    if y & 1: z ^= x
                    y >>= 1; x <<= 1
                    if x & q: x ^= mod
                T[a, b] = z
        self.MUL = T
        self.INV = np.zeros(q, dtype=np.int64)
        for x in range(1, q):
            self.INV[x] = int(np.nonzero(T[x] == 1)[0][0])
        self.wt = np.array([bin(x).count('1') for x in range(q)], dtype=np.int64)

    def pow(self, x, e):
        """vectorised power over F_q (x array)."""
        x = np.asarray(x, dtype=np.int64); y = np.ones_like(x)
        while e:
            if e & 1: y = self.MUL[y, x]
            x = self.MUL[x, x]; e >>= 1
        return y


def ring_ops(m):
    q = 1 << m; mask = q - 1
    def add(x, y):
        a, c = x & mask, y & mask
        return (a ^ c) | ((((x >> m) ^ (y >> m) ^ (a & c)) & mask) << m)
    def neg(x):
        a = x & mask
        return a | (((a ^ (x >> m)) & mask) << m)
    def sub(x, y): return add(x, neg(y))
    def J(x): return ((x & mask) << m) | (x >> m)
    return add, neg, sub, J


def ring_mul_digits(m, X, Y):
    """X, Y: (..., m) Z4 digit arrays; product in Z4[t]/(f)."""
    f = MOD[m]
    conv = np.zeros(X.shape[:-1] + (2 * m - 1,), dtype=np.int64)
    for i in range(m):
        conv[..., i:i + m] += X[..., i:i + 1] * Y
    conv %= 4
    for k in range(2 * m - 2, m - 1, -1):          # t^k = t^(k-m) * t^m,  t^m = -(f - t^m)
        top = conv[..., k].copy(); conv[..., k] = 0
        for j in range(m):
            if f[j]:
                conv[..., k - m + j] = (conv[..., k - m + j] - top) % 4
    return conv[..., :m] % 4


def codes_to_digits(m, x):
    x = np.asarray(x, dtype=np.int64)
    lo = (x[..., None] >> np.arange(m)) & 1
    hi = (x[..., None] >> (m + np.arange(m))) & 1
    return lo + 2 * hi


def digits_to_codes(m, c):
    c = np.asarray(c, dtype=np.int64) % 4
    w = (1 << np.arange(m)).astype(np.int64)
    return (c & 1) @ w + ((c >> 1) @ w << m)


def natural_exponents(m, r=3):
    V = [1 << i for i in range(0, r - 2)]
    W = 1 << (r - 2); Y = 1 << (m - 2); Z = 1 << (m - 1)
    return sorted(set(V) | {W} | {W + v for v in V} | {W + Y, W + Z} | {Y + v for v in V} | {Y + Z})


def natural_table(m, r=3):
    """F(x) = sum_{e in E} x^e evaluated in GR(4,m) for all N elements (own ring arithmetic)."""
    N = 1 << (2 * m)
    X = codes_to_digits(m, np.arange(N))
    E = natural_exponents(m, r); emax = max(E)
    acc = np.zeros_like(X); cur = np.zeros_like(X); cur[..., 0] = 1
    for e in range(1, emax + 1):
        cur = ring_mul_digits(m, cur, X)
        if e in E: acc = (acc + cur) % 4
    return digits_to_codes(m, acc)


def pd_table(K, p, h, d):
    m, q = K.m, K.q; N = q * q
    x = np.arange(N); a = x & (q - 1); b = x >> m
    return p[a] | ((h[a] ^ K.MUL[d[a], b]) << m)


def extract_pd(K, F):
    """Recover (p,h,d) from a table and verify the PD form and hypotheses (H).  Returns dict."""
    m, q = K.m, K.q; N = q * q; mask = q - 1
    x = np.arange(N); a = x & mask; b = x >> m
    p = F[:q] & mask
    assert np.array_equal(F & mask, p[a]), 'lo digit depends on b'
    h = F[:q] >> m
    d = (F[np.arange(q) | (1 << m)] >> m) ^ h
    assert np.array_equal(F >> m, h[a] ^ K.MUL[d[a], b]), 'hi digit not h(a)+d(a)b'
    return check_pd(K, p, h, d)


def check_pd(K, p, h, d):
    m, q = K.m, K.q; A = np.arange(q)
    assert len(np.unique(p)) == q, 'p not a permutation'
    for u in range(1, q):                                   # APN: D_u p is exactly 2-to-1
        cnt = np.bincount(p[A ^ u] ^ p, minlength=q)
        assert cnt.max() == 2 and set(np.unique(cnt)) <= {0, 2}, 'p not APN'
    Kl = d ^ d[0]
    for u in range(q):
        assert np.all((d[A ^ u] ^ d) == Kl[u]), 'd not F2-affine'
    assert np.all(d != 0), 'd has a zero'
    ker = [u for u in range(q) if Kl[u] == 0]
    assert len(ker) == 2, 'ker K != {0,rho}'
    rho = ker[1]
    assert d[0] not in set(Kl.tolist()), 'eps in Im K'
    return {'p': p, 'h': h, 'd': d, 'K': Kl, 'rho': rho}


def ddt(m, B):
    add, neg, sub, J = ring_ops(m)
    N = len(B); X = np.arange(N); C = np.empty((N, N), dtype=np.int64)
    for al in range(N):
        C[al] = np.bincount(sub(B[add(X, al)], B), minlength=N)
    assert np.all(C.sum(0) == N) and np.all(C.sum(1) == N)
    return C


def build_lifts(K, which):
    """PD tables used for calibration.  Returns dict name -> (F, info string)."""
    m, q = K.m, K.q; A = np.arange(q); out = {}
    rng = np.random.default_rng(20261011 + m)
    Fn = natural_table(m, 3)
    nat = extract_pd(K, Fn)
    inv = K.pow(A, q - 2)                                   # a^{-1}, 0 -> 0
    d0 = K.MUL[K.MUL[A, A], K.MUL[A, A]] ^ K.MUL[A, A] ^ 1  # a^4 + a^2 + 1
    a3 = K.pow(A, 3)
    hr = rng.integers(0, q, q)
    if 'natural' in which: out['natural_P%d3' % m] = Fn
    if 'h0' in which: out['natural_h0'] = pd_table(K, nat['p'], np.zeros(q, np.int64), nat['d'])
    if 'random' in which: out['natural_hrand'] = pd_table(K, nat['p'], hr, nat['d'])
    if 'inv' in which:
        out['inv_h0'] = pd_table(K, inv, np.zeros(q, np.int64), d0)
        out['inv_ha'] = pd_table(K, inv, A.copy(), d0)
        out['inv_ha3'] = pd_table(K, inv, a3, d0)
    if 'rho' in which:
        # d(a) = L(a / rho) + 1, L(y) = y^4 + y^2  =>  ker K = {0, rho},  no zeros (m odd)
        for rho, pname, p in ((3, 'inv', inv), (0b10101 if m == 5 else 0b1010101, 'gold', a3)):
            y = K.MUL[A, K.INV[rho]]
            dd = K.MUL[K.MUL[y, y], K.MUL[y, y]] ^ K.MUL[y, y] ^ 1
            hh = rng.integers(0, q, q)
            out['%s_rho%d_hrand' % (pname, rho)] = pd_table(K, p, hh, dd)
    return out, Fn
