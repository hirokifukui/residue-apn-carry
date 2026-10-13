"""P8-07 extra calibration. Usage: t3_extra.py CODE_DIR OUT_DIR PART
PART in {split5, adv, m7, bframe, msurvey}.  All finite numerics = calibration (VERIFIED_FINITE)."""
import sys, json, time
import numpy as np
sys.path.insert(0, sys.argv[1])
from gcore import Field, PD, d0_K, random_K, formula_G, atoms, M_mult, is_apn_perm
from t2_analyze import pair_data, spec

OUT = sys.argv[2]
PART = sys.argv[3]


def wht1(X):
    n, k = X.shape
    h = 1
    while h < n:
        Y = X.reshape(n // (2 * h), 2, h, k)
        X = np.stack([Y[:, 0] + Y[:, 1], Y[:, 0] - Y[:, 1]], axis=1).reshape(n, k)
        h *= 2
    return X


def wht2(X):
    """unnormalised Walsh-Hadamard transform along both axes of a (q,q) array (natural order)."""
    X = np.asarray(X, dtype=np.float64)
    return wht1(wht1(X).T.copy()).T.copy()


def n_table(P):
    F = P.F; q = F.q
    a = np.arange(q)
    keys = []
    for u in P.U:
        kin = int(F.inv[int(P.K[u])])
        keys.append((P.p[a ^ u] ^ P.p) * q + F.mul[P.d, kin])
    return np.bincount(np.concatenate(keys), minlength=q * q).reshape(q, q)  # [y, nu]


def B0_norm(P, n, z, dense_max=2200):
    """||B0_z|| via n_z and the convolution structure; dense if dim small, else Lanczos."""
    F = P.F; q, m = F.q, F.m
    nu = np.arange(q)
    L = np.zeros(q, dtype=np.int64)
    for j in range(m):
        L |= F.par[z & F.mul[nu, 1 << j]] << j
    nz = np.zeros((q, q)); nz[:, L] = n  # nz[y, ell]
    S = np.repeat(np.arange(q), q); X = np.tile(np.arange(q), q)
    sel = (S & X) == z
    xi, s = X[sel], S[sel]  # cols(z)
    dim = len(xi)
    if dim <= dense_max:
        nh = wht2(nz)  # nh[alpha, beta] = sum n_z(y,ell)(-1)^{alpha.y+beta.ell}
        Mx = nh[xi[:, None] ^ xi[None, :], s[:, None] ^ s[None, :]]
        return float(np.linalg.eigvalsh(Mx)[-1]), dim
    from scipy.sparse.linalg import LinearOperator, eigsh

    def mv(v):
        Xa = np.zeros((q, q)); Xa[xi, s] = np.ravel(v)
        Y = wht2(nz * wht2(Xa)) / 1.0  # conv(nh, Xa) = WHT(n_z * WHT(Xa))
        return Y[xi, s]
    op = LinearOperator((dim, dim), matvec=mv, dtype=np.float64)
    w = eigsh(op, k=1, which='LA', tol=1e-6, return_eigenvectors=False)
    return float(w[0]), dim


def std_cases(F, rng, with_random=2):
    q = F.q
    pinv = F.power(q - 2)
    cs = []
    for rho in (1, 0b111):
        K, eps = d0_K(F, rho)
        cs.append((f"inv,d0(rho={rho})", pinv, K, eps))
    for j in range(with_random):
        K, eps = random_K(F, rng)
        cs.append((f"inv,randomK#{j}", pinv, K, eps))
    p3 = F.power(3)
    if is_apn_perm(F, p3):
        K, eps = d0_K(F, 1)
        cs.append(("x^3,d0(rho=1)", p3, K, eps))
    return cs


rng = np.random.default_rng(80703)
res = {}
t0 = time.time()

if PART == "split5":
    for m in (3, 5):
        F = Field(m); q = F.q
        K, eps = d0_K(F, 1)
        P = PD(F, F.power(q - 2), K, eps, rng.integers(0, q, size=q))
        R = len(P.U) * (q - 1)
        cats = ["same_atom", "same_coset", "sameu_rest", "cross_delta0", "cross_rest"]
        acc = {(v, c): np.zeros(R) for v in ("V0", "V2", "V3", "EX") for c in cats}
        pw3 = 3.0 ** np.arange(m + 1)
        for d in pair_data(P):
            z = d["z"]; row, ell, phi, y, ui, a, u = d["row"], d["ell"], d["phi"], d["y"], d["ui"], d["a"], d["u"]
            dl = y[:, None] ^ y[None, :]; lam = ell[:, None] ^ ell[None, :]; w = z | dl
            V0 = pw3[m - F.wt[w]]; V2 = pw3[m - F.wt[w | lam]]
            sd = 1 - 2 * F.par[z & dl]; sl = 1 - 2 * F.par[lam & w]
            EX = (1 - 2 * (phi[:, None] ^ phi[None, :])) * sd * sl * V2
            V3 = sd * V2
            su = ui[:, None] == ui[None, :]; x = a[:, None] ^ a[None, :]
            sa = su & (x == 0)
            sc = su & ((x == P.rho) | (x == u[:, None]) | (x == (u[:, None] ^ P.rho)))
            masks = dict(same_atom=sa, same_coset=sc, sameu_rest=su & ~sa & ~sc, cross_delta0=~su & (dl == 0),
                         cross_rest=~su & (dl != 0))
            for c, mk in masks.items():
                for vn, V in (("V0", V0), ("V2", V2), ("V3", V3), ("EX", EX)):
                    # row sums of |kernel| restricted to the category, aggregated into row r (abs per (r,r') later is
                    # not separable; here we record sum over pairs of |term| -> majorant row sums)
                    acc[(vn, c)] += np.bincount(row, weights=(np.abs(V) * mk).sum(1), minlength=R)
        tab = {}
        for (vn, c), arr in acc.items():
            tab.setdefault(vn, {})[c] = float(arr.max()) / q ** 4
        res[f"m{m}"] = dict(q=q, note="max over rows of sum over atom pairs of |term| (per category), /q^4", table=tab)
        print(m, json.dumps(tab), flush=True)

elif PART == "adv":
    for m, nev in ((3, 400), (5, 120)):
        F = Field(m); q = F.q
        for rho in (1, 0b111):
            K, eps = d0_K(F, rho)
            pinv = F.power(q - 2)
            best = -1; besth = None; trace = []
            ev = 0
            while ev < nev:
                h = rng.integers(0, q, size=q); cur = None
                for it in range(nev // 4):
                    if ev >= nev:
                        break
                    h2 = h.copy()
                    if cur is not None:
                        h2[rng.integers(q)] = rng.integers(q)
                    P = PD(F, pinv, K, eps, h2)
                    val = float(np.linalg.norm(formula_G(P).astype(float), 2)) / q
                    ev += 1
                    if cur is None or val >= cur:
                        h, cur = h2, val
                    if cur > best:
                        best, besth = cur, h.copy()
                trace.append(cur)
            P = PD(F, pinv, K, eps, besth)
            n = n_table(P)
            B0 = max(B0_norm(P, n, z)[0] for z in range(1, q))
            res[f"m{m}_rho{rho}"] = dict(q=q, evaluations=ev, best_q_MG=best, best_h=besth.tolist(),
                                         restart_finals=trace, hfree_bound_q_MG=float(np.sqrt(q * B0)) / q,
                                         hfree_bound_MG2_times_q=B0 / q ** 2, M_pd=int(n.max()))
            print(m, rho, best, float(np.sqrt(q * B0)) / q, flush=True)

elif PART == "m7":
    from scipy.sparse.linalg import svds
    m = 7; F = Field(m); q = F.q
    for name, p, K, eps in std_cases(F, rng, with_random=1)[:3]:
        for hname in ("0", "rand"):
            h = np.zeros(q, dtype=np.int64) if hname == "0" else rng.integers(0, q, size=q)
            P = PD(F, p, K, eps, h)
            t1 = time.time()
            nU = len(P.U)
            Sx = np.repeat(np.arange(q), q - 1); Xx = np.tile(np.arange(1, q), q); Zx = Sx & Xx
            nzm = Zx != 0; cols = np.nonzero(nzm)[0]; Sc, Xc, Zc = Sx[nzm], Xx[nzm], Zx[nzm]
            g = np.zeros((nU * (q - 1), q * (q - 1)), dtype=np.float32)
            cache = {}
            for (ui, u, a, A, mu, y, ha, E) in atoms(P):
                if A not in cache:
                    cache[A] = F.adjT(A)
                eta = cache[A][Zc]
                C = ha ^ F.mul[mu, Sc ^ E]
                sg = F.par[Xc & y] ^ F.par[Zc & C]
                g[ui * (q - 1) + eta - 1, cols] += (1 - 2 * sg).astype(np.float32)
            sv = svds(g, k=1, return_singular_vectors=False, tol=1e-6)[0]
            gu2 = []
            for i in range(nU):
                blk = g[i * (q - 1):(i + 1) * (q - 1)]
                gu2.append(float(np.linalg.eigvalsh((blk @ blk.T).astype(np.float64))[-1]))
            # sampled majorant row sums (V0, V2, V3) for 12 rows
            pdz = pair_data(P)
            byz = {d["z"]: d for d in pdz}
            pw3 = 3.0 ** np.arange(m + 1)
            rs = {"V0": [], "V2": []}
            for r in rng.choice(nU * (q - 1), size=12, replace=False):
                tot = {k: 0.0 for k in rs}
                for z, d in byz.items():
                    I = np.nonzero(d["row"] == r)[0]
                    if len(I) == 0:
                        continue
                    dl = d["y"][I][:, None] ^ d["y"][None, :]
                    lam = d["ell"][I][:, None] ^ d["ell"][None, :]
                    w = z | dl
                    tot["V0"] += pw3[m - F.wt[w]].sum(); tot["V2"] += pw3[m - F.wt[w | lam]].sum()
                for k in rs:
                    rs[k].append(tot[k] / q ** 4)
            n = n_table(P)
            res[f"{name},h={hname}"] = dict(m=m, q=q, normg2=float(sv ** 2), q_MG=float(sv / q), sqrtq_MG=float(sv / q ** 1.5),
                                            MG2_times_q=float(sv ** 2 / q ** 3),
                                            max_u_normgu2_over_q2=max(gu2) / q ** 2, sum_u_normgu2_over_q3=sum(gu2) / q ** 3,
                                            sampled_rowsum_V0_over_q4_max=max(rs["V0"]),
                                            sampled_rowsum_V2_over_q4_max=max(rs["V2"]),
                                            C7_bound_MG2=4 * (1.5 ** m - 1) / q, M_pd=int(n.max()), sec=round(time.time() - t1, 1))
            print(json.dumps(res[f"{name},h={hname}"]), flush=True)
            del g

elif PART == "bframe":
    for m in (5, 7, 9):
        F = Field(m); q = F.q
        for name, p, K, eps in std_cases(F, rng, with_random=2):
            P = PD(F, p, K, eps, np.zeros(q, dtype=np.int64))
            n = n_table(P)
            if m <= 7:
                zs = list(range(1, q))
            else:
                zs = [1 << j for j in range(m)] + [int(z) for z in rng.integers(1, q, size=6)]
                zs = [z for z in zs if F.wt[z] <= 1 or (3 ** (m - F.wt[z]) <= 2200)]
            vals = []
            for z in zs:
                v, dim = B0_norm(P, n, z)
                vals.append((int(F.wt[z]), v / q ** 2, dim))
            byw = {}
            for wv, r, dim in vals:
                byw[str(wv)] = max(byw.get(str(wv), 0), r)
            res[f"m{m},{name}"] = dict(m=m, q=q, M_pd=int(n.max()), maxB0_over_q2=max(v[1] for v in vals),
                                       by_wt=byw, n_z_tested=len(zs),
                                       implied_bound_MG2_times_q=max(v[1] for v in vals))
            print(json.dumps(res[f"m{m},{name}"]), flush=True)

elif PART == "msurvey":
    for m in (3, 5, 7, 9, 11):
        F = Field(m); q = F.q
        ps = {"inv": F.power(q - 2), "x^3": F.power(3), "x^5": F.power(5), "x^13(Kasami k=2)": F.power(13)}
        for pn, p in ps.items():
            if not is_apn_perm(F, p):
                res[f"m{m},{pn}"] = "not APN permutation"
                continue
            Ks = [("d0(rho=1)",) + d0_K(F, 1), ("d0(rho=7)",) + d0_K(F, 0b111)]
            for j in range(6):
                Ks.append((f"randomK#{j}",) + random_K(F, rng))
            for kn, K, eps in Ks:
                P = PD(F, p, K, eps, np.zeros(q, dtype=np.int64))
                n = n_table(P)
                res[f"m{m},{pn},{kn}"] = dict(m=m, M=int(n.max()), rho=P.rho)
            print(m, pn, [res[f"m{m},{pn},{kn}"]["M"] for kn, _, _ in Ks], flush=True)

res["_sec"] = round(time.time() - t0, 1)
json.dump(res, open(f"{OUT}/t3_{PART}.json", "w"), indent=1)
print("DONE", PART)
