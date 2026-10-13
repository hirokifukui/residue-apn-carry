"""P3-06 (C3, Claude): research candidates after the C2 review. Independent-key model only (no key schedule).
Reuses c2/macro/macro_ref.py arithmetic (Ring, SBox, Macro.S/Sinv, mixers) WITHOUT modifying it.

  CANDIDATE_P3A_SUFFIX (GPT NEW_DERIVATIONS C.1, minimal C = F^w):
      E_A(x) = C( M2 . E_SB(x) + L2 ),  E_SB = S_2^(2) o tau_L o M o S_2^(1) (C2 macro with t=2, whitening k0),  C in {F, B, S1(k3)} wordwise
      cost: F 7w, J 4w, M twice  (C=F)
  CANDIDATE_P3B_THREE (Claude, after the P3-15 zero-sum finding):
      E_B(x) = S_2^(3)( M2 . E_SB(x) + L2 )      three S_2 layers, two mixings, resets L, L2
      cost: F 9w, J 6w, M twice
Both keep the averaged differential bound (4/N)^w by D1 + warm start (first two layers) and the reset post-composition lemma (P3-05).
"""
import os, sys
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.normpath(os.path.join(HERE, '..', '..', 'c2', 'macro')))
from macro_ref import Macro, mixers   # noqa: E402


class P3:
    def __init__(self, m, w, M, M2=None, kind='A', suffix='F', r=3):
        self.base = Macro(m, r, w, 2, M)          # t = 2 local blocks
        self.rg, self.sb = self.base.rg, self.base.sb
        self.w, self.kind, self.suffix = w, kind, suffix
        self.M2 = [[int(v) for v in row] for row in (M2 if M2 is not None else M)]
        self.M2inv = self.rg.mat_inv(self.M2)

    def random_keys(self, rng):
        k = self.base.random_keys(rng); N, w = self.rg.N, self.w
        k['L2'] = rng.integers(0, N, w).tolist()
        if self.kind == 'B':
            k['K3'] = rng.integers(0, N, (w, 2)).tolist()
        elif self.suffix == 'S1':
            k['K3'] = rng.integers(0, N, (w, 1)).tolist()
        return k

    def pre_suffix(self, xs, keys):
        """state entering the final wordwise layer: M2 . E_SB(x) + L2."""
        ys = self.base.enc(xs, keys)
        v = self.rg.mat_apply(self.M2, ys)
        return [self.rg.add(v[j], keys['L2'][j]) for j in range(self.w)]

    def final(self, z, j, keys):
        if self.kind == 'B':
            return self.base.S(z, keys['K3'][j])
        if self.suffix == 'F': return self.sb.F[z]
        if self.suffix == 'B': return self.sb.B[z]
        return self.base.S(z, keys['K3'][j])        # S1 = F(B(z)+k3)

    def final_inv(self, y, j, keys):
        if self.kind == 'B':
            return self.base.Sinv(y, keys['K3'][j])
        if self.suffix == 'F': return self.sb.Finv(y)
        if self.suffix == 'B': return self.sb.Binv(y)
        return self.base.Sinv(y, keys['K3'][j])

    def enc(self, xs, keys):
        z = self.pre_suffix([np.asarray(x, dtype=np.int64) for x in xs], keys)
        return [self.final(z[j], j, keys) for j in range(self.w)]

    def dec(self, ys, keys):
        z = [self.rg.sub(self.final_inv(np.asarray(ys[j], dtype=np.int64), j, keys), keys['L2'][j]) for j in range(self.w)]
        u = self.rg.mat_apply(self.M2inv, z)
        return self.base.dec(u, keys)

    def counts(self):
        w = self.w
        if self.kind == 'A':
            extra_F = w if self.suffix in ('F', 'B', 'S1') else 0
            extra_F += w if self.suffix == 'S1' else 0
            extra_J = w if self.suffix == 'B' else (w if self.suffix == 'S1' else 0)
            return {'F': 6 * w + extra_F, 'J': 4 * w + extra_J, 'M': 2,
                    'key_words': {'k0': w, 'K1': 2 * w, 'L': w, 'K2': 2 * w, 'L2': w, 'K3': (w if self.suffix == 'S1' else 0)}}
        return {'F': 9 * w, 'J': 6 * w, 'M': 2, 'key_words': {'k0': w, 'K1': 2 * w, 'L': w, 'K2': 2 * w, 'L2': w, 'K3': 2 * w}}
