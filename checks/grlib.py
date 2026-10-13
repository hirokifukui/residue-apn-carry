"""grlib.py -- C8 (Claude, 2026-10-12): small independent library for the C8 checks.
GF(2^m) arithmetic (ints = bit vectors in the polynomial basis), GR(4,m) two-digit carry
arithmetic, the PD layer B = J o F and its DDT with RING differences.  Written from the paper
definitions (sec_2 Lemma 2.1, B(a,b) = (h(a) xor d(a) b, p(a))); it does not import any C1..C7 code.
"""
import numpy as np

POLY = {3: 0b1011, 5: 0b100101, 7: 0b10000011, 9: 0b1000010001, 11: 0b100000000101}


class GF:
    def __init__(self, m, poly=None):
        self.m = m
        self.q = 1 << m
        self.poly = POLY[m] if poly is None else poly
        q = self.q
        mul = np.zeros((q, q), dtype=np.int64)
        for a in range(q):
            for b in range(q):
                mul[a, b] = self._mul(a, b)
        self.mul = mul
        inv = np.zeros(q, dtype=np.int64)
        for a in range(1, q):
            inv[a] = int(np.nonzero(mul[a] == 1)[0][0])
        self.inv = inv  # inv[0] = 0, i.e. x^(q-2)

    def _mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a & self.q:
                a ^= self.poly
        return r

    def pw(self, a, e):
        r = 1
        for _ in range(e):
            r = int(self.mul[r, a])
        return r

    def tr(self, a):
        s, x = 0, a
        for _ in range(self.m):
            s ^= x
            x = int(self.mul[x, x])
        return s  # 0 or 1


def popcount(x):
    return bin(int(x)).count("1")


def dot(x, y):
    return popcount(int(x) & int(y)) & 1


def ring_add(x, y, m):
    """x, y as (a, b) with ints; carry a & u into the high digit."""
    return (x[0] ^ y[0], x[1] ^ y[1] ^ (x[0] & y[0]))


def ring_sub(y, z):
    s = y[0] ^ z[0]
    return (s, y[1] ^ z[1] ^ (z[0] & s))


def d0_table(K):
    """d0(a) = (a^2 + a + 1)^2."""
    q = K.q
    return np.array([int(K.mul[t, t]) for t in [int(K.mul[a, a]) ^ a ^ 1 for a in range(q)]], dtype=np.int64)


def ddt_B(K, p, d, h):
    """integer DDT of B = J o F over ring differences; states indexed i = a + q*b."""
    q = K.q
    N = q * q
    idx = np.arange(N)
    A = idx % q
    Bh = idx // q
    # B(a, b) = (h(a) ^ d(a) b, p(a))
    lo = h[A] ^ K.mul[d[A], Bh]
    hi = p[A]
    D = np.zeros((N, N), dtype=np.int64)
    for al in range(N):
        u, v = al % q, al // q
        # x + alpha
        a2 = A ^ u
        b2 = Bh ^ v ^ (A & u)
        lo2 = h[a2] ^ K.mul[d[a2], b2]
        hi2 = p[a2]
        s = lo2 ^ lo
        t = hi2 ^ hi ^ (lo & s)
        np.add.at(D[al], s + q * t, 1)
    return D
