"""C5 attack lane (ATK, Claude 2026-10-11): shared setup for P5-10 / P5-03 small-group calibration.

NEW file.  Everything in c1/c2/c3/c4 is imported read-only and NOT modified.
Small m (1..4) are not in c1 ringlib.MODULI / c2 macro_ref.F_FILES, so this module REGISTERS extra entries in those
dicts at RUNTIME ONLY (in-memory, the source files are untouched):
    ringlib.MODULI[m]  : monic Z4 lift of an F_2-irreducible polynomial (checked by ringlib.f2_irreducible)
    macro_ref.F_FILES  : (m, r) -> absolute path of an S-box table saved by this lane (needed only because
                         Macro.__init__ loads a table before SplitTail swaps in `ftable`).
The cipher itself is the C4 reference implementation c4/macro/macro_p4.py :: SplitTail (imported, unchanged).

Secrecy contract (P5-10): the key is generated INSIDE make_cipher_oracle and is only reachable through the
closure; the attack receives `query` (chosen-plaintext encryption) and the PUBLIC parameters (m, w, M3^{-1},
S-box table) only.  `reveal` is handed to the scorer, which is called after the attack has returned and its
output has been hashed (commit-then-reveal).
"""
import os, sys, json, hashlib
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
APN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
ATK = os.path.normpath(os.path.join(HERE, '..'))
DATA = os.path.join(ATK, 'results', 'data')
sys.path.insert(0, os.path.join(APN, 'c4', 'macro'))
sys.path.insert(0, os.path.join(APN, 'c2', 'macro'))
sys.path.insert(0, os.path.join(APN, 'c1', 'code'))
import ringlib                                    # noqa: E402  (same module object macro_ref uses)
import macro_ref                                  # noqa: E402
from macro_p4 import SplitTail                    # noqa: E402

EXTRA_MODULI = {1: (1, 1), 2: (1, 1, 1), 3: (1, 1, 0, 1), 4: (1, 1, 0, 0, 1)}   # t+1, t^2+t+1, t^3+t+1, t^4+t+1
for _m, _f in EXTRA_MODULI.items():
    assert ringlib.f2_irreducible(_f), _m
    ringlib.MODULI.setdefault(_m, _f)


def sha_arr(a):
    return hashlib.sha256(np.ascontiguousarray(np.asarray(a).astype(np.int64)).tobytes()).hexdigest()


def sha_file(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


# ---------------------------------------------------------------- S-box tables  F(a,b) = (p(a), h(a) xor d(a) b)
def _field(m):
    return ringlib.GF2m(m)


def table_from_phd(m, p, h, d):
    K = _field(m); q = 1 << m; N = q * q
    X = np.arange(N); a = X & (q - 1); b = X >> m
    return (np.asarray(p)[a] | ((np.asarray(h)[a] ^ K.MUL[np.asarray(d)[a], b]) << m)).astype(np.int64)


def natural_table(m, r):
    """natural sigma-lift of P_{m,r} (ringlib.P_exponents), Horner over GR(4,m) -- as c1/code/t303_oracle.py."""
    R = ringlib.GR4(m)
    e = ringlib.P_exponents(m, r)
    return R.encode(R.horner(e, R.all)).astype(np.int64), sorted(e)


def pd_inverse_table(m, hkind, eps=1):
    """PD type: p = x^{-1} (0->0), d = X^4 + X^2 + eps, h = 0 / a^3."""
    K = _field(m); q = 1 << m
    inv = np.array([K.pow(a, q - 2) if a else 0 for a in range(q)], dtype=np.int64)
    d = np.array([K.pow(a, 4) ^ K.pow(a, 2) ^ eps for a in range(q)], dtype=np.int64)
    h = np.zeros(q, np.int64) if hkind == 'h0' else np.array([K.pow(a, 3) for a in range(q)], dtype=np.int64)
    return table_from_phd(m, inv, h, d)


def toy_m2_table():
    """m=2 toy (NOT PD: every permutation of F_4 is affine, so no APN permutation exists).
    p(a) = a^2 + 1, d(a) = a^2 + a + w (w = t, Tr(w)=1 so d has no zero), h(a) = a^3."""
    K = _field(2); q = 4
    p = np.array([K.pow(a, 2) ^ 1 for a in range(q)], dtype=np.int64)
    d = np.array([K.pow(a, 2) ^ a ^ 2 for a in range(q)], dtype=np.int64)
    h = np.array([K.pow(a, 3) for a in range(q)], dtype=np.int64)
    return table_from_phd(2, p, h, d)


def decompose(T, m):
    q = 1 << m; a = np.arange(q)
    p = T[a] & (q - 1); h = T[a] >> m; d = (T[a | (1 << m)] >> m) ^ h
    return p, h, d


def hypotheses(T, m):
    """PD / W2 hypotheses checked directly from the table: form, p perm, DU(p), d affine, ker K, eps not in Im K."""
    K = _field(m); q = 1 << m; N = q * q
    p, h, d = decompose(T, m)
    form = bool(np.array_equal(table_from_phd(m, p, h, d), T))
    perm_p = len(set(p.tolist())) == q
    du = 0
    for u in range(1, q):
        du = max(du, int(np.bincount(p ^ p[np.arange(q) ^ u], minlength=q).max()))
    eps = int(d[0]); Kl = d ^ eps
    affine = all(int(Kl[a ^ c]) == int(Kl[a]) ^ int(Kl[c]) for a in range(q) for c in range(q))
    ker = [a for a in range(q) if Kl[a] == 0]
    ImK = set(Kl.tolist())
    return {'form_(p,h+db)': form, 'p_perm': perm_p, 'DU_p': du, 'p_APN': bool(perm_p and du == 2),
            'd_affine': bool(affine), 'ker_K': ker, 'eps': eps, 'eps_notin_ImK': eps not in ImK,
            'd_nowhere_zero': bool(np.all(d != 0)), 'F_perm': len(set(T.tolist())) == N,
            'h_zero': bool(np.all(h == 0)),
            'PD_hypotheses': bool(form and perm_p and du == 2 and affine and len(ker) == 2 and eps not in ImK)}


def save_table(name, T):
    os.makedirs(DATA, exist_ok=True)
    p = os.path.join(DATA, name + '.npy')
    if not os.path.exists(p):
        np.save(p, np.asarray(T, dtype=np.int64))
    assert np.array_equal(np.load(p), T), 'saved table differs: ' + p
    return p


def build_cipher(m, w, table_path, M):
    """C4 SplitTail with S-box table at table_path; registers F_FILES[(m,99)] at runtime (in memory)."""
    macro_ref.F_FILES[(m, 99)] = table_path
    c = SplitTail(m, w, M, M, M, r=99, ftable=table_path)
    assert np.array_equal(c.sb.F, np.load(table_path))
    return c


# ---------------------------------------------------------------- public parameters (no key material)
class Public:
    """What the attacker is allowed to know: m, w, the S-box table, M3^{-1}.  Built from the cipher object
    BEFORE any key exists (SplitTail holds no key)."""
    def __init__(self, c):
        self.m, self.w = c.m, c.w
        self.rg, self.sb = c.rg, c.sb
        self.N = c.rg.N
        self.M3inv = [[int(v) for v in row] for row in c.M3inv]


# ---------------------------------------------------------------- oracles (key closed inside)
def make_cipher_oracle(c, key_seed):
    """returns (query, reveal, counter).  query(list of w arrays) -> list of w arrays (chosen-plaintext enc)."""
    rng = np.random.default_rng([20261011, 510, key_seed, c.m, c.w])
    _k = c.random_keys(rng)                       # lives only in this closure
    cnt = {'queries': 0}

    def query(xs):
        cnt['queries'] += int(len(xs[0]))
        return [np.asarray(y, dtype=np.int64) for y in c.enc(xs, _k)]

    def reveal():
        return _k
    return query, reveal, cnt


def _flat(xs, N):
    v = np.zeros(len(xs[0]), dtype=object)
    idx = np.zeros(len(xs[0]), dtype=np.int64)
    for j in range(len(xs)):
        idx = idx * N + np.asarray(xs[j], dtype=np.int64)
    return idx


def make_random_oracle(N, w, seed, kind):
    """kind 'RF' (uniform random function R^w -> R^w) or 'RP' (uniform random permutation), lazily sampled."""
    rng = np.random.default_rng([20261011, 503, seed, N, w, 0 if kind == 'RF' else 1])
    table = {}; used = set(); cnt = {'queries': 0}
    tot = N ** w

    def query(xs):
        cnt['queries'] += int(len(xs[0]))
        n = len(xs[0]); out = np.zeros((w, n), dtype=np.int64)
        keys = list(zip(*[np.asarray(x).tolist() for x in xs]))
        for t, kx in enumerate(keys):
            if kx not in table:
                if kind == 'RF':
                    y = tuple(int(v) for v in rng.integers(0, N, w))
                else:
                    while True:
                        y = tuple(int(v) for v in rng.integers(0, N, w))
                        if y not in used: break
                    used.add(y)
                table[kx] = y
            out[:, t] = table[kx]
        return [out[j] for j in range(w)]
    return query, (lambda: None), cnt


def mds2():
    return [[1, 1], [1, 2]]


def random_unit_matrix(rg, w, seed):
    """invertible w x w over R with every entry a unit (so a one-word slice keeps property P)."""
    rng = np.random.default_rng([20261011, 503, 7, rg.m, w, seed])
    while True:
        M = [[int(v) for v in rng.integers(0, rg.N, w)] for _ in range(w)]
        if not all(rg.is_unit(v) for row in M for v in row):
            continue
        try:
            rg.mat_inv(M)
        except ValueError:
            continue
        return M
