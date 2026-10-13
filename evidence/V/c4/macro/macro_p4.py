"""P4-05 (C4, Claude 2026-10-11): reference implementation of CANDIDATE_P4_SPLIT_TAIL (local lengths (2,2,1,1)).
Research toy, independent-key model only (no key schedule).  Proposed by the GPT C3 audit (NEW_DERIVATIONS B);
this file is Claude's own implementation.  Arithmetic is REUSED from c2/macro/macro_ref.py (Ring, SBox, Macro.S/Sinv,
mixers), which in turn reuses c1 -- it is NOT an independent arithmetic implementation.  c1/c2/c3 are not modified.

  S_t(x; k_1..k_t) = F( B( ... B( B(x) + k_1 ) ... ) + k_t ),  B = J o F          (same as c2/c3)
  E(x) = S1^(4)( M3 . S1^(3)( M2 . S2^(2)( M1 . S2^(1)(x + k0) + L1 ) + L2 ) + L3 )   (wordwise S layers)

  states:  X1 = S2^(1)(x+k0),  V1 = M1 X1 + L1,  X2 = S2^(2)(V1),  V2 = M2 X2 + L2   ("V3" in the GPT audit),
           X3 = S1^(3)(V2),     V3 = M3 X3 + L3   ("V4" in the GPT audit),  Y = S1^(4)(V3)
  keys:    k0 (w), K1 (w x 2), L1 (w), K2 (w x 2), L2 (w), K3 (w x 1), L3 (w), K4 (w x 1)   -> 10w ring words
  cost:    F 10w, J 6w, M 3.

Optional `ftable` replaces the S-box table F (same (p,h,d) form required, checked by SBox) -- used for the PD
control (P4-08).  The state names follow the audit numbering in `states()` keys 'x2','v3','x3','v4' as well.
"""
import os, sys
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
APN = os.path.normpath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(APN, 'c2', 'macro'))
from macro_ref import Macro, SBox, mixers   # noqa: E402


class SplitTail:
    def __init__(self, m, w, M1, M2=None, M3=None, r=3, ftable=None):
        self.base = Macro(m, r, w, 2, M1)               # S2 - M1/L1 - S2 with whitening k0
        if ftable is not None:
            self.base.sb = SBox(self.base.rg, ftable)
        self.rg, self.sb = self.base.rg, self.base.sb
        self.m, self.w = m, w
        self.M1 = self.base.M
        self.M2 = [[int(v) for v in row] for row in (M2 if M2 is not None else M1)]
        self.M3 = [[int(v) for v in row] for row in (M3 if M3 is not None else M1)]
        self.M2inv, self.M3inv = self.rg.mat_inv(self.M2), self.rg.mat_inv(self.M3)

    def random_keys(self, rng):
        N, w = self.rg.N, self.w
        k = self.base.random_keys(rng)                  # k0, K1 (w x 2), L (=L1), K2 (w x 2)
        k['L2'] = rng.integers(0, N, w).tolist(); k['K3'] = rng.integers(0, N, (w, 1)).tolist()
        k['L3'] = rng.integers(0, N, w).tolist(); k['K4'] = rng.integers(0, N, (w, 1)).tolist()
        return k

    def _lin(self, M, xs, L):
        v = self.rg.mat_apply(M, xs)
        return [self.rg.add(v[j], L[j]) for j in range(self.w)]

    def states(self, xs, k):
        xs = [np.asarray(x, dtype=np.int64) for x in xs]
        x2 = self.base.enc(xs, k)                        # X2 = output of the second S2 layer
        v2 = self._lin(self.M2, x2, k['L2'])
        x3 = [self.base.S(v2[j], k['K3'][j]) for j in range(self.w)]
        v3 = self._lin(self.M3, x3, k['L3'])
        y = [self.base.S(v3[j], k['K4'][j]) for j in range(self.w)]
        return {'X2': x2, 'V2': v2, 'X3': x3, 'V3': v3, 'Y': y,
                'x2': x2, 'v3': v2, 'x3': x3, 'v4': v3}        # audit names

    def enc(self, xs, k):
        return self.states(xs, k)['Y']

    def dec(self, ys, k):
        rg, w = self.rg, self.w
        ys = [np.asarray(y, dtype=np.int64) for y in ys]
        v3 = [rg.sub(self.base.Sinv(ys[j], k['K4'][j]), k['L3'][j]) for j in range(w)]
        x3 = rg.mat_apply(self.M3inv, v3)
        v2 = [rg.sub(self.base.Sinv(x3[j], k['K3'][j]), k['L2'][j]) for j in range(w)]
        x2 = rg.mat_apply(self.M2inv, v2)
        return self.base.dec(x2, k)

    def counts(self):
        w = self.w
        return {'F': 10 * w, 'J': 6 * w, 'M': 3,
                'key_words': {'k0': w, 'K1': 2 * w, 'L1': w, 'K2': 2 * w, 'L2': w, 'K3': w, 'L3': w, 'K4': w, 'total': 10 * w}}


def ringsum(a, m):
    """ring sum of an array of codes (coefficientwise mod 4)."""
    a = np.asarray(a, dtype=np.int64); lo = hi = 0
    for j in range(m):
        c = int(np.sum(((a >> j) & 1) + 2 * ((a >> (m + j)) & 1))) % 4
        lo |= (c & 1) << j; hi |= (c >> 1) << j
    return lo | (hi << m)
