# Independent brute-force audit of Theorem G / Lemma P / blocks, m=3,5.
# DDT of B in Z4 coordinates -> physical projections (no Walsh) -> tau, ||M_G||, ||M_E||, ||M_Z||;
# Walsh g from DDT; Psi*Sigma from the claimed formula; Sigma Sigma^T block structure vs closed form.
import sys, json, os, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from acore import GF, ALT_POLYS, ddt_B, physical_blocks, walsh_g, M_count, linK_from_coeffs, popc, ip, pd_check

out = sys.argv[1]; mlist = [int(t) for t in sys.argv[2].split(",")]
rng = np.random.default_rng(7)


def adj(F, A, z):
    """M_A^* z : (M_A^* z)_i = <z, A e_i>"""
    r = 0
    for i in range(F.m):
        if ip(z, int(F.mul(A, 1 << i))): r |= 1 << i
    return r


def atoms_data(F, p, d, h, K, rho):
    q = F.q; a = np.arange(q)
    U = [u for u in range(q) if u not in (0, rho)]
    rows = []
    for u in U:
        k = int(K[u])
        mu = F.div(d[a], np.full(q, k))
        A = F.mul(mu, d[a ^ u])
        y = p[a ^ u] ^ p[a]
        E = h[a ^ u] ^ h[a] ^ F.mul(d[a ^ u], a & u)
        for ai in range(q):
            rows.append((u, ai, int(mu[ai]), int(A[ai]), int(y[ai]), int(E[ai])))
    return U, rows


def formula_checks(F, p, d, h, K, rho, gbrute):
    q, m = F.q, F.m
    U, rows = atoms_data(F, p, d, h, K, rho)
    nat = len(rows)
    rowidx = {u: i for i, u in enumerate(U)}
    gform = np.zeros((len(U), q - 1, q, q - 1))
    maxB0 = 0.0; maxB = 0.0; closed_ok = True; offdiag_zero = True
    for z in range(1, q):
        cols = [(s, xi) for s in range(q) for xi in range(1, q) if (s & xi) == z]
        S = np.array([c[0] for c in cols]); X = np.array([c[1] for c in cols])
        Sig = np.zeros((nat, len(cols))); Sig0 = np.zeros((nat, len(cols)))
        eps = np.zeros(nat); ell = np.zeros(nat, dtype=np.int64); yv = np.zeros(nat, dtype=np.int64)
        Psi_eta = np.zeros(nat, dtype=np.int64)
        for i, (u, ai, mu, A, y, E) in enumerate(rows):
            C = h[ai] ^ F.mul(np.full(len(S), mu), S ^ E)  # C_{u,a}(s)
            Sig[i] = (-1.0) ** (ip(X, y) ^ ip(S & X, C))
            l = adj(F, mu, z); ell[i] = l; yv[i] = y
            e = ip(z, h[ai] ^ int(F.mul(mu, E)))
            eps[i] = (-1.0) ** e
            Sig0[i] = (-1.0) ** (ip(X, y) ^ ip(S, l))
            Psi_eta[i] = adj(F, A, z)
        # Lemma P
        if not np.array_equal(Sig, eps[:, None] * Sig0):
            closed_ok = False; print("LEMMA P FAIL z", z)
        # Psi Sigma accumulate
        for i, (u, ai, mu, A, y, E) in enumerate(rows):
            eta = Psi_eta[i]
            assert eta != 0
            for c, (s, xi) in enumerate(cols):
                gform[rowidx[u], eta - 1, s, xi - 1] += Sig[i, c]
        # Sigma Sigma^T block vs closed form
        Bz = Sig @ Sig.T
        dl = yv[:, None] ^ yv[None, :]; lm = ell[:, None] ^ ell[None, :]
        w = z | dl
        B0c = ((-1.0) ** (ip(z, dl) ^ ip(lm, w))) * (3.0 ** (m - popc(w | lm)))
        if not np.array_equal(Sig0 @ Sig0.T, B0c):
            closed_ok = False; print("CLOSED FORM FAIL z", z)
        if not np.array_equal(Bz, eps[:, None] * B0c * eps[None, :]):
            closed_ok = False; print("E B0 E FAIL z", z)
        nb0 = np.linalg.eigvalsh(B0c).max(); nb = np.linalg.eigvalsh(Bz).max()
        maxB0 = max(maxB0, nb0); maxB = max(maxB, nb)
    # off-diagonal z-blocks of Sigma Sigma^T are structurally zero: column sets {s&xi=z} disjoint.
    g_eq = np.array_equal(gform, gbrute)
    return g_eq, closed_ok, maxB0, maxB


def run_case(F, pname, p, Kname, K, eps, hname, h, do_formula=True):
    q, m = F.q, F.m
    rho = pd_check(F, p, K, eps)
    d = eps ^ K
    t0 = time.time()
    D = ddt_B(F, p, d, h)
    N = q * q
    assert (D.sum(1) == N).all() and (D.sum(0) == N).all()
    tau, nG, nE, nZ = physical_blocks(F, D, rho)
    Gw, U, gfull = walsh_g(F, D, rho)
    gi = np.rint(Gw)
    assert np.abs(Gw - gi).max() < 1e-6
    # G rows reach s=0 or xi=0 ? (claim: no)
    g_s0 = np.abs(gfull[U][:, 1:, 0, :]).max(); g_xi0 = np.abs(gfull[U][:, 1:, :, 0]).max()
    gG = gi[:, :, 1:, :].reshape(len(U) * (q - 1), -1)
    ng_w = np.linalg.norm(gG, 2) / q ** 2
    M = M_count(F, p, d, K, rho)
    rec = dict(m=m, poly=F.poly, p=pname, K=Kname, rho=rho, wt_rho=int(popc(rho)), eps=eps, h=hname,
               tau2=tau ** 2, MG2=nG ** 2, ME2=nE ** 2, MZ2=nZ ** 2, q_MG=q * nG,
               MG_walsh=ng_w, MG_phys_eq_walsh=bool(abs(ng_w - nG) < 1e-9),
               G_to_s0_or_xi0_max=float(max(g_s0, g_xi0)),
               M=M, bound_MG2=M / q, MG2_le_Mq=bool(nG ** 2 <= M / q + 1e-12),
               ME2_le_3q=bool(nE ** 2 <= 3 / q + 1e-12),
               MZ2_exact=(q / 2 - 1) / q ** 2, MZ2_eq=bool(abs(nZ ** 2 - (q / 2 - 1) / q ** 2) < 1e-12),
               tau2_le_sum=bool(tau ** 2 <= nG ** 2 + nE ** 2 + nZ ** 2 + 1e-12),
               tau2_le_claim=bool(tau ** 2 <= (M + 3) / q + (q / 2 - 1) / q ** 2 + 1e-12))
    if do_formula:
        g_eq, closed_ok, maxB0, maxB = formula_checks(F, p, d, h, K, rho, gi)
        g2 = np.linalg.norm(gG, 2) ** 2
        rec.update(g_eq_PsiSigma=bool(g_eq), closed_form_ok=bool(closed_ok),
                   maxB0_over_q2=maxB0 / q ** 2, maxB_eq_maxB0=bool(abs(maxB - maxB0) < 1e-6 * maxB0),
                   chain_ok=bool(g2 <= q * maxB0 * (1 + 1e-9) and maxB0 <= q * q * M * (1 + 1e-9)))
    rec["secs"] = round(time.time() - t0, 1)
    print(json.dumps(rec), flush=True)
    return rec


def K0rho(F, rho):
    ir = int(F.inv(rho))
    return linK_from_coeffs(F, [0, int(F.pw(ir, 2)), int(F.pw(ir, 4))])


res = []
for m in mlist:
    for poly in ([None] + ([ALT_POLYS[m]] if m in ALT_POLYS else [])):
        F = GF(m, poly); q = F.q; x = np.arange(q)
        ps = [("inv", F.inv(x)), ("x^3", F.pw(x, 3))]
        Ks = [("K0", K0rho(F, 1)), ("K0(x/7)", K0rho(F, 7))]
        if m == 5: Ks.append(("K0(x/11)", K0rho(F, 11)))
        hs = [("0", np.zeros(q, dtype=np.int64)), ("a^3", F.pw(x, 3)), ("rand", rng.integers(0, q, q))]
        for pname, p in ps:
            for Kname, K in Ks:
                for hname, h in hs:
                    if poly is not None and not (pname == "inv" and hname != "0"): continue
                    if m == 5 and pname == "x^3" and hname == "0": continue
                    res.append(run_case(F, pname, p, Kname, K, 1, hname, h))
json.dump(res, open(out, "w"), indent=1)
bad = [r for r in res if not all(v for k, v in r.items() if isinstance(v, bool))]
print("cases", len(res), "bad", len(bad))
