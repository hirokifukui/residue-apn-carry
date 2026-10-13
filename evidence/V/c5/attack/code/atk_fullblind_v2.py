"""C5 ATK lane (v2: disjoint slices): full-blind candidate attack on CANDIDATE_P4_SPLIT_TAIL (local lengths (2,2,1,1), three mixings).

The attack sees ONLY  query(xs) -> ys  and the public parameters (atk_common.Public: m, w, S-box table, M3^{-1}).
It never touches a key object (this module does not import the oracle factories).

Candidate family (NEW_DERIVATIONS C):  theta = (K4_0..K4_{w-1}, c_0..c_{w-1}, K3_0..K3_{w-1}),  N^{3w} candidates,
    G_theta(y)_j = S1^{-1}( (M3^{-1} S1^{-1}(y;K4))_j - c_j ; K3_j )        (S1^{-1}(u;k) = B^{-1}(F^{-1}(u) - k))
accept theta  iff  for every one-word slice t and every word j:  sum_x G_theta(E(x))_j = 0 in R.
Decomposition used (and only this one): for each K4 tuple kappa (outer loop, all N^w), and each target word j
separately, the set A_j(kappa) of (c_j, K3_j) passing all slices; theta accepted iff c_j,K3_j in A_j(kappa) for all j.
So the accepted set is the disjoint union over kappa of the products  A_0(kappa) x ... x A_{w-1}(kappa).

Kernel (exact, no FFT): for fixed kappa, j, slice: z_x = (M3^{-1} V3(x))_j,  D(v) = #{x : z_x = v},
    T_i[k, c] = sum_u Gc_i[k, u] * D(u + c)  =  sum_x coef_i( S1^{-1}(z_x - c; k) )
computed as one real matrix product per coefficient i (float64).  Every intermediate is an integer of absolute
value <= 3 N * N < 2^53, hence represented exactly and every add/mul is exact (no rounding, any summation order).
(k, c) passes the slice iff T_i[k, c] = 0 mod 4 for all i = 0..m-1.
"""
import os, sys, time, json, hashlib, resource
sys.dont_write_bytecode = True
import numpy as np


class Kernel:
    def __init__(self, pub):
        self.pub = pub; rg, sb = pub.rg, pub.sb
        self.m, self.w, self.N = pub.m, pub.w, pub.N
        m, N = self.m, self.N
        codes = np.arange(N, dtype=np.int64)
        self.ADD = rg.add(codes[:, None], codes[None, :])                         # [u, c] -> u + c
        self.Ginv = sb.Binv(rg.sub(sb.Finv(codes)[None, :], codes[:, None]))     # [k, u] -> S1^{-1}(u; k)
        self.Gc = np.stack([(((self.Ginv >> i) & 1) + 2 * ((self.Ginv >> (m + i)) & 1)).astype(np.float64)
                            for i in range(m)])                                      # (m, N_k, N_u)
        self.MUL = {int(v): rg.mulc(v) for row in pub.M3inv for v in row}
        self.ops = {'S1inv_lookups': 0, 'matmul_mult_adds': 0, 'z_ring_ops': 0, 'histograms': 0}

    def V3(self, Y, kap):
        """Y: list of w arrays (n,), kap: (B, w) -> list of w arrays (B, n)."""
        self.ops['S1inv_lookups'] += kap.shape[0] * self.w * len(Y[0])
        return [self.Ginv[kap[:, i]][:, Y[i]] for i in range(self.w)]

    def z(self, j, V):
        rg = self.pub.rg; Mi = self.pub.M3inv[j]
        acc = self.MUL[Mi[0]][V[0]]
        for i in range(1, self.w):
            acc = rg.add(acc, self.MUL[Mi[i]][V[i]])
        self.ops['z_ring_ops'] += V[0].size * (2 * self.w - 1)
        return acc

    def accept(self, z):
        """z: (B, n) codes -> bool (B, N_k, N_c): sum_x S1^{-1}(z_x - c; k) == 0 in R."""
        B, n = z.shape; N, m = self.N, self.m
        D = np.zeros((B, N), np.float64)
        np.add.at(D, (np.repeat(np.arange(B), n), z.ravel()), 1.0)
        self.ops['histograms'] += B
        Dsh = D[:, self.ADD]                                                         # (B, N_u, N_c)
        ok = np.ones((B, N, N), bool)
        for i in range(m):
            T = np.matmul(self.Gc[i], Dsh)                                           # (B, N_k, N_c)
            ok &= (np.rint(T).astype(np.int64) & 3) == 0
        self.ops['matmul_mult_adds'] += B * m * N * N * N
        return ok

    def accept_literal(self, z, k, c):
        """direct definition for one (k, c): used only by self-tests."""
        rg = self.pub.rg
        v = self.Ginv[k][rg.sub(np.asarray(z, np.int64), c)]
        m = self.m
        return all(int((((v >> i) & 1) + 2 * ((v >> (m + i)) & 1)).sum()) % 4 == 0 for i in range(m))


def make_slices(N, w, s, slice_seed, active=0):
    """attacker-chosen one-word slices (public randomness only).  v2: the constant tuples of the inactive words are
    drawn WITHOUT replacement, so the s slices are pairwise disjoint (v1 drew them with replacement and could repeat
    a slice, e.g. seed 6 at m=3 repeated slice 3 as slice 4)."""
    rng = np.random.default_rng([20261011, 510, 6, slice_seed, N, w, 2])
    flat = rng.choice(N ** (w - 1), size=s, replace=False)
    consts = np.zeros((s, w), np.int64)
    pos = [j for j in range(w) if j != active]
    for t in range(s):
        f = int(flat[t])
        for j in reversed(pos):
            consts[t, j] = f % N; f //= N
    X = np.arange(N, dtype=np.int64)
    return [[X if j == active else np.full(N, int(consts[t, j]), np.int64) for j in range(w)] for t in range(s)], consts


def all_tuples(N, w, lo=0, hi=None):
    hi = N ** w if hi is None else hi
    idx = np.arange(lo, hi, dtype=np.int64)
    out = np.empty((idx.size, w), np.int64)
    for i in range(w - 1, -1, -1):
        out[:, i] = idx % N; idx = idx // N
    return out


def attack(query, pub, s, slice_seed, batch=256, enum_cap=200000, kappa_range=None, log=None):
    """full-blind: every K4, c, K3 unknown.  Returns dict with per-slice counts and the accepted candidate set
    (as kappa -> per-target lists of (c, K3)), plus T/D/M.  No key is read."""
    t0 = time.perf_counter(); c0 = time.process_time()
    N, w, m = pub.N, pub.w, pub.m
    ker = Kernel(pub)
    slices, consts = make_slices(N, w, s, slice_seed)
    Ys = [query(q) for q in slices]                                                  # D = s N chosen plaintexts
    lo, hi = (0, N ** w) if kappa_range is None else kappa_range
    kappa_alive = [0] * (s + 1); kappa_alive[0] = hi - lo
    pairs = [[0] * w for _ in range(s)]                                              # sum_kappa |A_j(kappa)| after t
    theta = [0] * s                                                                  # sum_kappa prod_j |A_j(kappa)|
    final = {}                                                                       # kappa_index -> [list per j]
    peak_bytes = 0
    for b0 in range(lo, hi, batch):
        kap = all_tuples(N, w, b0, min(b0 + batch, hi)); kid = np.arange(b0, min(b0 + batch, hi))
        ok = None
        for t in range(s):
            if kap.shape[0] == 0: break
            V = ker.V3(Ys[t], kap)
            okt = np.stack([ker.accept(ker.z(j, V)) for j in range(w)], 1)            # (B, w, N_k, N_c)
            peak_bytes = max(peak_bytes, okt.nbytes * 2 + kap.shape[0] * N * N * 8 * 2)
            ok = okt if ok is None else ok & okt
            cnt = ok.reshape(ok.shape[0], w, -1).sum(-1)                              # (B, w)
            for j in range(w): pairs[t][j] += int(cnt[:, j].sum())
            theta[t] += int(sum(int(np.prod([int(v) for v in row])) for row in cnt))
            alive = np.all(cnt > 0, 1)
            kap, kid, ok = kap[alive], kid[alive], ok[alive]
            kappa_alive[t + 1] += int(alive.sum())
        if kap.shape[0] and ok is not None and ok.shape[0]:
            for r in range(kap.shape[0]):
                final[int(kid[r])] = [[(int(cc), int(kk)) for kk, cc in zip(*np.nonzero(ok[r, j]))] for j in range(w)]
        if log and (b0 - lo) % (batch * 64) == 0:
            log(f'kappa {b0}/{hi} alive_after_slices={kappa_alive[1:]} theta={theta} {time.perf_counter() - t0:.1f}s')
    # enumerate accepted theta (capped) ---------------------------------------------------------------
    cands = []
    for kidx, lists in sorted(final.items()):
        kv = all_tuples(N, w, kidx, kidx + 1)[0].tolist()
        def rec(j, acc):
            if len(cands) >= enum_cap: return
            if j == w:
                cands.append({'K4': kv, 'c': [a[0] for a in acc], 'K3': [a[1] for a in acc]}); return
            for pr in lists[j]: rec(j + 1, acc + [pr])
        rec(0, [])
    res = {'s': s, 'slice_seed': slice_seed, 'slice_consts_sha256': hashlib.sha256(consts.tobytes()).hexdigest(),
           'kappa_range': [lo, hi],
           'K4_tuples_alive_after_slice': kappa_alive, 'pairs_per_target_after_slice': pairs,
           'theta_accepted_after_slice': theta, 'expected_theta_RF_after_slice': [float(N) ** ((3 - (t + 1)) * w) for t in range(s)],
           'candidate_exists': theta[-1] > 0, 'n_candidates_enumerated': len(cands), 'candidates': cands,
           'T_wall_s': round(time.perf_counter() - t0, 3), 'T_cpu_s': round(time.process_time() - c0, 3),
           'ops': dict(ker.ops), 'D_queries': s * N,
           'M_peak_working_arrays_bytes_est': int(peak_bytes),
           'M_maxrss': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    return res


def commit(res):
    return hashlib.sha256(json.dumps(res, sort_keys=True, default=str).encode()).hexdigest()


# ------------------------------------------------------------------ evaluation helpers (need G_theta only)
def G_theta(ker, theta, ys):
    """literal G_theta on a list of w arrays."""
    pub = ker.pub; rg = pub.rg; w = pub.w
    V = [ker.Ginv[theta['K4'][i]][np.asarray(ys[i], np.int64)] for i in range(w)]
    out = []
    for j in range(w):
        Mi = pub.M3inv[j]; acc = ker.MUL[Mi[0]][V[0]]
        for i in range(1, w): acc = rg.add(acc, ker.MUL[Mi[i]][V[i]])
        out.append(ker.Ginv[theta['K3'][j]][rg.sub(acc, theta['c'][j])])
    return out
