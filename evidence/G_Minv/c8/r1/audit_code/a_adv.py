# Adversarial search: (1) m=3 brute-force DDT, random APN perms (affine-equivalent to x^3 / inverse),
# random K with 1-dim kernel, random eps not in Im K, hill-climbing h to maximise ||M_G||;
# (2) m=5 hill-climbing h with the (brute-force-validated) formula g, p=inverse, d0-type.
import sys, json, os, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from acore import GF, ddt_B, physical_blocks, M_count, linK_from_coeffs, popc, ip, pd_check, walsh_g

out = sys.argv[1]; mode = sys.argv[2]
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)


def rand_invertible(m):
    while True:
        A = rng.integers(0, 2, (m, m))
        B = A.copy(); r = 0
        for c in range(m):
            pv = [i for i in range(r, m) if B[i, c]]
            if not pv: continue
            B[[r, pv[0]]] = B[[pv[0], r]]
            for i in range(m):
                if i != r and B[i, c]: B[i] ^= B[r]
            r += 1
        if r == m: return A


def apply_lin(A, x, m):
    cols = [int(sum(int(A[i, j]) << i for i in range(m))) for j in range(m)]
    return np.array([np.bitwise_xor.reduce([cols[j] for j in range(m) if xx >> j & 1] or [0]) for xx in x])


def rand_K(F):
    m, q = F.m, F.q
    while True:
        A = rng.integers(0, 2, (m, m))
        K = apply_lin(A, np.arange(q), m)
        if sum(1 for t in K if t == 0) == 2: return K


def MG_phys(F, p, d, h, rho):
    D = ddt_B(F, p, d, h)
    return physical_blocks(F, D, rho)


res = []
if mode == "m3":
    F = GF(3); q = F.q; x = np.arange(q)
    worst = 0.0
    for trial in range(int(sys.argv[4]) if len(sys.argv) > 4 else 40):
        base = F.pw(x, 3) if trial % 2 == 0 else F.inv(x)
        A1, A2 = rand_invertible(3), rand_invertible(3)
        c1, c2 = int(rng.integers(q)), int(rng.integers(q))
        p = apply_lin(A2, base[apply_lin(A1, x, 3) ^ c1], 3) ^ c2
        K = rand_K(F); im = set(K.tolist())
        eps = int(rng.choice([t for t in range(q) if t not in im]))
        rho = pd_check(F, p, K, eps); d = eps ^ K
        M = M_count(F, p, d, K, rho)
        h = rng.integers(0, q, q)
        cur = MG_phys(F, p, d, h, rho)[1] ** 2
        for it in range(300):
            h2 = h.copy(); h2[rng.integers(q)] = rng.integers(q)
            v = MG_phys(F, p, d, h2, rho)[1] ** 2
            if v >= cur: h, cur = h2, v
        tau, nG, nE, nZ = MG_phys(F, p, d, h, rho)
        rec = dict(trial=trial, M=M, MG2=nG ** 2, bound=M / q, ratio=nG ** 2 * q / M, ME2=nE ** 2,
                   MZ2=nZ ** 2, tau2=tau ** 2, tau2_claim_bound=(M + 3) / q + (q / 2 - 1) / q ** 2,
                   ok=bool(nG ** 2 <= M / q + 1e-12 and nE ** 2 <= 3 / q + 1e-12
                           and abs(nZ ** 2 - (q / 2 - 1) / q ** 2) < 1e-12), h=h.tolist(), p=p.tolist(),
                   K=K.tolist(), eps=eps)
        worst = max(worst, rec["ratio"])
        print(json.dumps({k: v for k, v in rec.items() if k not in ("h", "p", "K")}), flush=True)
        res.append(rec)
    print("max ratio ||M_G||^2 q / M =", worst)
elif mode == "m5":
    F = GF(5); q = F.q; m = 5; x = np.arange(q)
    p = F.inv(x)
    ir = 1
    configs = [("K0", 1), ("K0(x/7)", 7), ("K0(x/11)", 11)]
    # precompute pair tables
    S = np.repeat(x, q); X = np.tile(x, q)
    Z = S & X; valid = (Z != 0) & (X != 0)
    S, X, Z = S[valid], X[valid], Z[valid]
    colidx = S * (q - 1) + (X - 1)
    adjtab = {}
    def adjvec(A):
        # returns array over z of M_A^* z
        if A in adjtab: return adjtab[A]
        cols = np.array([int(F.mul(A, 1 << i)) for i in range(m)])
        r = np.zeros(q, dtype=np.int64)
        for i in range(m):
            r |= ip(x, cols[i]) << i
        adjtab[A] = r; return r
    for name, rho in configs:
        irho = int(F.inv(rho))
        K = linK_from_coeffs(F, [0, int(F.pw(irho, 2)), int(F.pw(irho, 4))])
        eps = 1; rho_ = pd_check(F, p, K, eps); assert rho_ == rho
        d = eps ^ K; M = M_count(F, p, d, K, rho)
        U = [u for u in range(q) if u not in (0, rho)]
        def gmat(h):
            g = np.zeros((len(U), q, q * (q - 1)))
            for ui, u in enumerate(U):
                k = int(K[u])
                for a in range(q):
                    mu = int(F.div(d[a], k)); A = int(F.mul(mu, d[a ^ u]))
                    y = p[a ^ u] ^ p[a]; E = h[a ^ u] ^ h[a] ^ int(F.mul(d[a ^ u], a & u))
                    C = h[a] ^ F.mul(np.full(len(S), mu), S ^ E)
                    sg = (-1.0) ** (ip(X, y) ^ ip(Z, C))
                    eta = adjvec(A)[Z]
                    np.add.at(g[ui], (eta, colidx), sg)
            return g[:, 1:, :].reshape(len(U) * (q - 1), -1)
        # validate formula g against brute force for one random h
        h0 = rng.integers(0, q, q)
        Gw, U2, _ = walsh_g(F, ddt_B(F, p, d, h0), rho)
        gb = np.rint(Gw).reshape(len(U) * (q - 1), -1)  # all s (s=0 cols are zero)
        assert np.array_equal(gmat(h0), gb), "formula g != brute"
        h = rng.integers(0, q, q)
        cur = np.linalg.norm(gmat(h), 2) ** 2 / q ** 4
        best_hist = [cur]
        t0 = time.time()
        for it in range(int(sys.argv[4]) if len(sys.argv) > 4 else 150):
            h2 = h.copy()
            for _ in range(int(rng.integers(1, 3))):
                h2[rng.integers(q)] = rng.integers(q)
            v = np.linalg.norm(gmat(h2), 2) ** 2 / q ** 4
            if v >= cur: h, cur = h2, v
            best_hist.append(cur)
        # final brute-force physical confirmation
        tau, nG, nE, nZ = physical_blocks(F, ddt_B(F, p, d, h), rho)
        rec = dict(K=name, rho=rho, M=M, MG2_formula=cur, MG2_phys=nG ** 2, q_MG=q * nG, bound=M / q,
                   ratio=nG ** 2 * q / M, tau2=tau ** 2, ME2=nE ** 2, MZ2=nZ ** 2,
                   tau2_claim_bound=(M + 3) / q + (q / 2 - 1) / q ** 2, h=h.tolist(),
                   hist=best_hist[::10], secs=round(time.time() - t0))
        print(json.dumps({k: v for k, v in rec.items() if k not in ("h", "hist")}), flush=True)
        res.append(rec)
json.dump(res, open(out, "w"), indent=1)

if mode == "m5pd":
    # Theorem G for general PD data at m=5 (random affine-equivalent APN perms, random K, eps, h)
    F = GF(5); q = F.q; x = np.arange(q)
    for trial in range(int(sys.argv[4]) if len(sys.argv) > 4 else 6):
        base = [F.inv(x), F.pw(x, 3), F.pw(x, 5)][trial % 3]
        A1, A2 = rand_invertible(5), rand_invertible(5)
        c1, c2 = int(rng.integers(q)), int(rng.integers(q))
        p = apply_lin(A2, base[apply_lin(A1, x, 5) ^ c1], 5) ^ c2
        K = rand_K(F); im = set(K.tolist())
        eps = int(rng.choice([t for t in range(q) if t not in im]))
        rho = pd_check(F, p, K, eps); d = eps ^ K
        M = M_count(F, p, d, K, rho)
        h = rng.integers(0, q, q)
        tau, nG, nE, nZ = MG_phys(F, p, d, h, rho)
        rec = dict(trial=trial, rho=rho, M=M, MG2=nG ** 2, bound=M / q, ratio=nG ** 2 * q / M,
                   ME2=nE ** 2, MZ2=nZ ** 2, tau2=tau ** 2,
                   ok=bool(nG ** 2 <= M / q + 1e-12 and nE ** 2 <= 3 / q + 1e-12
                           and abs(nZ ** 2 - (q / 2 - 1) / q ** 2) < 1e-12))
        print(json.dumps(rec), flush=True); res.append(rec)
    json.dump(res, open(out, "w"), indent=1)
