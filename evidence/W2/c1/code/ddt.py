"""Integer difference tables over (R,+) for maps given as code tables (independent of GPT code)."""
import numpy as np
from codes import mk

def ddt(m, f):
    q = 1 << m; N = q * q; add, neg, sub, J = mk(m)
    X = np.arange(N); C = np.zeros((N, N), dtype=np.int64)
    for a in range(N):
        C[a] = np.bincount(sub(f[add(X, a)], f), minlength=N)
    return C

PRIMES = [1048573, 1048571, 1048559, 1048549, 1048517, 1048507, 1048447, 1048433]  # < 2^20, primes

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
assert all(is_prime(p) for p in PRIMES)

def modmat(A, p):
    """exact (A mod p) as float64."""
    return np.mod(A, p).astype(np.float64)

def mulmod(A, B, p):
    """A,B float64 with entries in [0,p), p<2^20, n<=1024: every partial sum < 2^50, exact in float64."""
    assert A.shape[1] <= 1024
    C = A @ B
    return np.fmod(C, p)

def crt(residues, primes):
    """residues: list of int arrays (same shape); returns object array of exact nonneg ints < prod(primes)."""
    M = 1
    for p in primes: M *= p
    out = np.zeros(residues[0].shape, dtype=object)
    for r, p in zip(residues, primes):
        Mi = M // p; inv = pow(Mi, -1, p)
        out = out + r.astype(np.int64).astype(object) * (Mi * inv)
    return np.mod(out, M), M
