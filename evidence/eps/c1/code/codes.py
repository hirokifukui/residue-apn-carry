"""Fast arithmetic on 2m-bit codes (lo bits 0..m-1 = digit-0 bits, hi bits m..2m-1 = digit-1 bits).
Validated against ringlib (coefficient arrays) in selftest()."""
import numpy as np

def mk(m):
    q = 1 << m; mask = q - 1
    def add(x, y):
        a, c = x & mask, y & mask
        return (a ^ c) | (((x >> m) ^ (y >> m) ^ (a & c)) << m)
    def neg(x):
        a = x & mask
        return a | ((a ^ (x >> m)) << m)
    def sub(x, y): return add(x, neg(y))
    def J(x): return ((x & mask) << m) | (x >> m)
    return add, neg, sub, J

def selftest(m, R, trials=20000, seed=1):
    add, neg, sub, J = mk(m)
    rng = np.random.default_rng(seed)
    x = rng.integers(0, R.N, trials); y = rng.integers(0, R.N, trials)
    X, Y = R.decode(x), R.decode(y)
    assert np.array_equal(add(x, y), R.encode(R.add(X, Y)))
    assert np.array_equal(sub(x, y), R.encode(R.sub(X, Y)))
    assert np.array_equal(neg(x), R.encode(R.neg(X)))
    return True
