"""C4 attack lane (Claude, 2026-10-11): shared helpers for P4-03 / P4-06.
Arithmetic is REUSED (not re-implemented): c2/macro/macro_ref.py (Ring, SBox, Macro), c3/macro/macro_p3.py (P3),
c4/macro/macro_p4.py (SplitTail).  Nothing in c1/c2/c3/c4/macro is modified.

Ring sums: a code v of R = GR(4,m) has coefficient c_i = lo_i + 2 hi_i in Z/4 (lo = bits 0..m-1, hi = bits m..2m-1).
The ring sum of a multiset is the coefficientwise sum mod 4.  The additive group (R,+) is Z4^m via these coefficients,
which is what the FFT correlation below uses.
"""
import os, sys, hashlib, json
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
APN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(APN, 'c4', 'macro'))
sys.path.insert(0, os.path.join(APN, 'c3', 'macro'))
sys.path.insert(0, os.path.join(APN, 'c2', 'macro'))
from macro_ref import Macro, SBox, mixers          # noqa: E402,F401
from macro_p3 import P3                            # noqa: E402,F401
from macro_p4 import SplitTail                     # noqa: E402,F401


def sha(obj):
    if isinstance(obj, np.ndarray):
        return hashlib.sha256(np.ascontiguousarray(obj.astype(np.int64)).tobytes()).hexdigest()
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()


def coef_sums(Z, m):
    """Z: int array (..., n) of codes -> int array (..., m) of coefficient sums mod 4 (ring sum, unpacked)."""
    Z = np.asarray(Z, dtype=np.int64)
    out = [((((Z >> i) & 1) + 2 * ((Z >> (m + i)) & 1)).sum(-1)) % 4 for i in range(m)]
    return np.stack(out, -1)


def ringsum(Z, m):
    """ring sum as a code (..., )."""
    c = coef_sums(Z, m)
    lo = np.zeros(c.shape[:-1], np.int64); hi = np.zeros(c.shape[:-1], np.int64)
    for i in range(m):
        lo |= (c[..., i] & 1) << i; hi |= (c[..., i] >> 1) << i
    return lo | (hi << m)


def xorsum(Z):
    return np.bitwise_xor.reduce(np.asarray(Z, dtype=np.int64), axis=-1)


def lo_xor(Z, m):
    return xorsum(np.asarray(Z, dtype=np.int64) & ((1 << m) - 1))


def S1inv_all_keys(sb, rg, y):
    """y: (n,) codes -> (N, n) array  [k, x] = S1^{-1}(y_x; k) = B^{-1}(F^{-1}(y_x) - k) for every k in R."""
    Fi = sb.Finv(np.asarray(y, dtype=np.int64))
    K = np.arange(rg.N, dtype=np.int64)
    return sb.Binv(rg.sub(Fi[None, :], K[:, None]))


class Z4Conv:
    """Exact correlation over (R,+) = Z4^m by FFT:  T_k(c) = sum_x g_k(z_x - c)  (coefficientwise),
    for g_k(u) = S1^{-1}(u; k) = B^{-1}(F^{-1}(u) - k) and all c in R at once, for a block of k values."""
    def __init__(self, rg, sb, ks):
        self.rg, self.sb, self.m, self.N = rg, sb, rg.m, rg.N
        m, N = self.m, self.N
        codes = np.arange(N, dtype=np.int64)
        cf = np.stack([((codes >> i) & 1) + 2 * ((codes >> (m + i)) & 1) for i in range(m)], -1)   # (N, m)
        self.idx = (cf * (4 ** np.arange(m))).sum(-1)          # code -> flat index in Z4^m
        self.code_of_idx = np.empty(N, np.int64); self.code_of_idx[self.idx] = codes
        self.shape = (4,) * m
        self.ks = np.asarray(ks, dtype=np.int64)
        # h_k(u) = g_k(-u); store fft of each coefficient of h_k, laid out in index space
        negu = rg.neg(codes)                                    # code of -u
        g = sb.Binv(rg.sub(sb.Finv(negu)[None, :], self.ks[:, None]))   # (K, N) : g_k(-u) at code u
        H = np.zeros((len(self.ks), m, N))
        for i in range(m):
            H[:, i, self.idx] = (((g >> i) & 1) + 2 * ((g >> (m + i)) & 1))
        self.Hhat = np.fft.fftn(H.reshape((len(self.ks), m) + self.shape), axes=tuple(range(2, 2 + m)))

    def zero_mask(self, z):
        """z: (n,) codes.  returns bool array (K, N): [k_index, c_code] -> sum_x g_k(z_x - c) == 0 in R."""
        m, N = self.m, self.N
        D = np.bincount(self.idx[np.asarray(z, dtype=np.int64)], minlength=N).astype(float)
        Dhat = np.fft.fftn(D.reshape(self.shape))
        T = np.fft.ifftn(self.Hhat * Dhat[None, None], axes=tuple(range(2, 2 + m))).real
        T = np.rint(T).astype(np.int64).reshape(len(self.ks), m, N) % 4
        ok_idx = np.all(T == 0, axis=1)                         # (K, N) in index space of c
        out = np.empty_like(ok_idx); out[:, self.code_of_idx] = ok_idx   # index -> code
        return out


def one_word_slice(N, w, active, consts):
    X = np.arange(N, dtype=np.int64)
    return [X if j == active else np.full(N, int(consts[j]), np.int64) for j in range(w)]
