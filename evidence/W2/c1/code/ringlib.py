"""ringlib.py -- independent GR(4,m) arithmetic for the apn_cipher C1 track (Claude, 2026-10-09).

Written without reading or importing GPT's check scripts or any earlier project module.
Shared with GPT's code ONLY the data definitions: modulus t^5+t^2+1 for m=5, the polynomial
P_{5,3}, and the 2m-bit code  idx = sum lo_i 2^i + sum hi_i 2^(m+i),  coefficient c_i = lo_i + 2 hi_i.

Representation here: an element is a length-m vector of Z/4 coefficients (numpy int64 rows).
Multiplication = schoolbook convolution + reduction by a precomputed table of t^j mod f(t) over Z/4
(a different route from GPT's in-place subtraction loop).
"""
import numpy as np

MODULI = {5: (1, 0, 1, 0, 0, 1),      # 1 + t^2 + t^5   (coefficients c_0..c_m)
          7: (1, 1, 0, 0, 0, 0, 0, 1),  # 1 + t + t^7
          9: (1, 0, 0, 0, 1, 0, 0, 0, 0, 1),            # 1 + t^4 + t^9
          11: (1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1),     # 1 + t^2 + t^11
          13: (1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1)}  # 1 + t + t^3 + t^4 + t^13


def f2_irreducible(coeffs):
    """trial division over F_2 (coeffs c_0..c_m)."""
    f = sum((c % 2) << i for i, c in enumerate(coeffs)); n = len(coeffs) - 1
    def pmod(a, b):
        db = b.bit_length() - 1
        while a and a.bit_length() - 1 >= db:
            a ^= b << (a.bit_length() - 1 - db)
        return a
    for g in range(2, 1 << (n // 2 + 1)):
        if g.bit_length() - 1 <= n // 2 and pmod(f, g) == 0:
            return False
    return True


class GR4:
    def __init__(self, m):
        self.m = m
        self.q = 1 << m
        self.N = self.q * self.q
        f = np.array(MODULI[m], dtype=np.int64)
        assert f[-1] == 1 and len(f) == m + 1
        # table t^j mod f over Z4, j = 0..2m-2
        red = np.zeros((2 * m - 1, m), dtype=np.int64)
        cur = np.zeros(m, dtype=np.int64); cur[0] = 1
        for j in range(2 * m - 1):
            red[j] = cur
            # multiply cur by t
            top = cur[-1]
            nxt = np.zeros(m, dtype=np.int64)
            nxt[1:] = cur[:-1]
            nxt = (nxt - top * f[:m]) % 4
            cur = nxt
        self.red = red
        self._all = None

    @property
    def all(self):
        """(N, m) coefficient table of every element (built on first use; only for small m)."""
        if self._all is None:
            assert self.m <= 8, 'full element table only for m <= 8'
            self._all = self.decode(np.arange(self.N, dtype=np.int64))
        return self._all

    # ---- encoding -------------------------------------------------------------
    def decode(self, idx):
        idx = np.asarray(idx, dtype=np.int64)
        m = self.m
        lo = (idx[..., None] >> np.arange(m)) & 1
        hi = (idx[..., None] >> (m + np.arange(m))) & 1
        return lo + 2 * hi

    def encode(self, c):
        c = np.asarray(c, dtype=np.int64) % 4
        m = self.m
        w_lo = (1 << np.arange(m)).astype(np.int64)
        w_hi = (1 << (m + np.arange(m))).astype(np.int64)
        return (c & 1) @ w_lo + (c >> 1) @ w_hi

    # ---- ring operations on coefficient arrays ---------------------------------
    def add(self, x, y): return (x + y) % 4
    def neg(self, x): return (-x) % 4
    def sub(self, x, y): return (x - y) % 4

    def mul(self, x, y):
        x = np.asarray(x); y = np.asarray(y)
        m = self.m
        shape = np.broadcast_shapes(x.shape, y.shape)
        x = np.broadcast_to(x, shape); y = np.broadcast_to(y, shape)
        conv = np.zeros(shape[:-1] + (2 * m - 1,), dtype=np.int64)
        for i in range(m):
            conv[..., i:i + m] += x[..., i:i + 1] * y
        return (conv % 4) @ self.red % 4

    def const(self, c):
        v = np.zeros(self.m, dtype=np.int64); v[0] = c % 4
        return v

    def is_unit(self, x):
        return np.any(np.asarray(x) % 2 != 0, axis=-1)

    def inv_unit(self, x):
        """inverse of a single unit (refuses non-units; no silent x^(q-1)... fallback)."""
        x = np.asarray(x, dtype=np.int64)
        if not self.is_unit(x):
            raise ValueError("inv_unit: argument is not a unit")
        prods = self.mul(self.all, x)
        hit = np.nonzero(np.all(prods == self.const(1), axis=-1))[0]
        assert len(hit) == 1
        return self.all[hit[0]]

    # ---- polynomial evaluation ---------------------------------------------------
    def horner(self, exps, xs):
        """sum_{e in exps} X^e evaluated (0/1 integer coefficients) at coefficient arrays xs."""
        deg = max(exps)
        acc = np.zeros_like(xs)
        one = self.const(1)
        for e in range(deg, -1, -1):
            acc = self.mul(acc, xs)
            if e in exps:
                acc = (acc + one) % 4
        return acc


class GF2m:
    """F_q = F_2[t]/(fbar), elements as m-bit ints (bit i = coefficient of t^i), independent table build."""
    def __init__(self, m):
        self.m = m; self.q = 1 << m
        f = MODULI[m]
        poly = sum((c % 2) << i for i, c in enumerate(f))
        q = self.q
        mul = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                r = 0; x = a; y = b
                while y:
                    if y & 1: r ^= x
                    y >>= 1; x <<= 1
                    if x & q: x ^= poly
                mul[a, b] = r
        self.MUL = mul

    def pow(self, a, e):
        r = 1
        while e:
            if e & 1: r = int(self.MUL[r, a])
            a = int(self.MUL[a, a]); e >>= 1
        return r


def P_exponents(m, r):
    """exponents of P_{m,r} = V+W+WV+WY+WZ+YV+YZ (Theorem A(1) of FFA-26-597)."""
    V = [1 << i for i in range(0, r - 2)]
    W = 1 << (r - 2); Y = 1 << (m - 2); Z = 1 << (m - 1)
    e = set(V) | {W} | {W + v for v in V} | {W + Y, W + Z} | {Y + v for v in V} | {Y + Z}
    assert len(e) == 3 * r - 2
    return e
