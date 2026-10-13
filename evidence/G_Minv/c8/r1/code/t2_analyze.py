"""Task (2)+(3) calibration: exact ||M_G||, Gram Q=g g^T, C7 majorant and variants, splits,
the h-free atom Grams B0_z and the multiplicity M(p,d).  Usage: t2_analyze.py CODE_DIR OUT_JSON m [m ...]
All numbers are finite calibration (VERIFIED_FINITE), not proofs.
"""
import sys, json, time
import numpy as np
sys.path.insert(0, sys.argv[1])
from gcore import Field, PD, d0_K, random_K, formula_G, atoms, M_mult, is_apn_perm


def spec(Msym):
    w = np.linalg.eigvalsh(Msym.astype(np.float64))
    return float(max(abs(w[0]), abs(w[-1])))


def pair_data(P):
    """Per z: atom arrays. Returns list of dicts."""
    F = P.F
    q, m = F.q, F.m
    at = atoms(P)
    ui = np.array([x[0] for x in at]); uu = np.array([x[1] for x in at]); aa = np.array([x[2] for x in at])
    AA = np.array([x[3] for x in at]); MU = np.array([x[4] for x in at]); YY = np.array([x[5] for x in at])
    HA = np.array([x[6] for x in at]); EE = np.array([x[7] for x in at])
    adjA = {A: F.adjT(A) for A in set(AA.tolist())}
    adjM = {mu: F.adjT(mu) for mu in set(MU.tolist())}
    res = []
    for z in range(1, q):
        eta = np.array([adjA[A][z] for A in AA])
        ell = np.array([adjM[mu][z] for mu in MU])
        phi = F.par[z & (HA ^ F.mul[MU, EE])]  # <z, h(a) + mu E_a>
        row = ui * (q - 1) + eta - 1
        res.append(dict(z=z, row=row, ell=ell, phi=phi, y=YY, ui=ui, u=uu, a=aa, A=AA))
    return res


def analyze(P, label, do_pairs=True):
    F = P.F
    q, m = F.q, F.m
    t0 = time.time()
    g = formula_G(P)
    R = g.shape[0]
    gf = g.astype(np.float64)
    sv = np.linalg.svd(gf, compute_uv=False)
    ng2 = float(sv[0] ** 2)
    out = dict(label=label, m=m, q=q, rho=P.rho, wt_rho=int(F.wt[P.rho]))
    out["normg2"] = ng2
    out["MG2"] = ng2 / q ** 4
    out["q_MG"] = float(sv[0] / q)
    out["sqrtq_MG"] = float(sv[0] / q ** 1.5)
    out["C7_bound_MG2"] = 4 * (1.5 ** m - 1) / q
    # per-u blocks
    nU = len(P.U)
    gu2 = [float(np.linalg.norm(gf[i * (q - 1):(i + 1) * (q - 1)], 2) ** 2) for i in range(nU)]
    out["max_u_normgu2_over_q2"] = max(gu2) / q ** 2
    out["sum_u_normgu2_over_q3"] = sum(gu2) / q ** 3
    out["frob2_over_q4"] = float((gf ** 2).sum()) / q ** 4
    Mval, _ = M_mult(P)
    out["M_pd"] = Mval
    out["new_bound_MG2_M_over_q"] = Mval / q
    if not do_pairs:
        out["sec"] = round(time.time() - t0, 1)
        return out
    Q = gf @ gf.T
    pdz = pair_data(P)
    nb = R * R
    acc = {k: np.zeros(nb) for k in ["exact", "V0", "V1", "V2", "V3",
                                      "p_same_atom", "p_same_coset", "p_delta0_cross", "p_rest_sameu", "p_rest_cross"]}
    B0max = 0.0
    B0ratio = []
    Bmax_with_eps = 0.0
    pw3 = 3.0 ** np.arange(m + 1)
    for d in pdz:
        z = d["z"]
        row, ell, phi, y, ui, a, u = d["row"], d["ell"], d["phi"], d["y"], d["ui"], d["a"], d["u"]
        dl = y[:, None] ^ y[None, :]
        lam = ell[:, None] ^ ell[None, :]
        w = z | dl
        mag_noλ = pw3[m - F.wt[w]]
        mag = pw3[m - F.wt[w | lam]]
        sgn_d = 1 - 2 * F.par[z & dl]
        sgn_l = 1 - 2 * F.par[lam & w]
        eps = 1 - 2 * (phi[:, None] ^ phi[None, :])
        ex0 = sgn_d * sgn_l * mag  # h-free atom Gram B0_z
        ex = eps * ex0
        idx = (row[:, None] * R + row[None, :]).ravel()
        acc["exact"] += np.bincount(idx, weights=ex.ravel(), minlength=nb)
        acc["V0"] += np.bincount(idx, weights=mag_noλ.ravel(), minlength=nb)
        acc["V1"] += np.bincount(idx, weights=(sgn_d * mag_noλ).ravel(), minlength=nb)
        acc["V2"] += np.bincount(idx, weights=mag.ravel(), minlength=nb)
        acc["V3"] += np.bincount(idx, weights=(sgn_d * mag).ravel(), minlength=nb)
        same_u = ui[:, None] == ui[None, :]
        same_atom = same_u & (a[:, None] == a[None, :])
        # same coset a' in a + <rho,u>
        x = a[:, None] ^ a[None, :]
        same_coset = same_u & ((x == 0) | (x == P.rho) | (x == u[:, None]) | (x == (u[:, None] ^ P.rho))) & ~same_atom
        delta0_cross = (~same_u) & (dl == 0)
        rest_sameu = same_u & ~same_atom & ~same_coset
        rest_cross = (~same_u) & (dl != 0)
        for key, mask in [("p_same_atom", same_atom), ("p_same_coset", same_coset), ("p_delta0_cross", delta0_cross),
                          ("p_rest_sameu", rest_sameu), ("p_rest_cross", rest_cross)]:
            acc[key] += np.bincount(idx, weights=(ex * mask).ravel(), minlength=nb)
        n0 = spec(ex0)
        n1 = spec(ex)
        B0max = max(B0max, n0)
        Bmax_with_eps = max(Bmax_with_eps, n1)
        B0ratio.append(dict(z=z, wt=int(F.wt[z]), B0=n0, B0_over_q2=n0 / q ** 2, B0_over_3mprime=n0 / 3 ** (m - F.wt[z])))
    Qex = acc["exact"].reshape(R, R)
    out["pair_formula_equals_ggT"] = bool(np.allclose(Qex, Q))
    out["maxabs_Qex_minus_ggT"] = float(np.abs(Qex - Q).max())
    for k in ["V0", "V1", "V2", "V3"]:
        Mk = acc[k].reshape(R, R)
        out[k] = dict(spec_over_q4=spec(Mk) / q ** 4, maxrowsum_abs_over_q4=float(np.abs(Mk).sum(1).max()) / q ** 4)
    out["V0_dominates_absQ"] = bool((np.abs(Q) <= acc["V0"].reshape(R, R) + 1e-9).all())
    out["V2_dominates_absQ"] = bool((np.abs(Q) <= acc["V2"].reshape(R, R) + 1e-9).all())
    out["Q_exact"] = dict(spec_over_q4=spec(Q) / q ** 4, maxrowsum_abs_over_q4=float(np.abs(Q).sum(1).max()) / q ** 4)
    # row-index splits of exact Q
    rui = np.repeat(np.arange(nU), q - 1)
    sameU = rui[:, None] == rui[None, :]
    D = np.diag(np.diag(Q))
    Su = np.where(sameU, Q, 0) - D
    Cx = np.where(~sameU, Q, 0)
    out["split_rows"] = {k: dict(spec_over_q4=spec(Mk) / q ** 4, maxrowsum_abs_over_q4=float(np.abs(Mk).sum(1).max()) / q ** 4)
                         for k, Mk in [("diag", D), ("sameu_offdiag", Su), ("cross_u", Cx)]}
    out["split_pairs"] = {k: dict(spec_over_q4=spec(acc[k].reshape(R, R)) / q ** 4,
                                  maxrowsum_abs_over_q4=float(np.abs(acc[k].reshape(R, R)).sum(1).max()) / q ** 4)
                          for k in ["p_same_atom", "p_same_coset", "p_delta0_cross", "p_rest_sameu", "p_rest_cross"]}
    out["B0_max_over_q2"] = B0max / q ** 2
    out["B_with_eps_max_over_q2"] = Bmax_with_eps / q ** 2
    out["check_normg2_le_q_maxB"] = bool(ng2 <= q * Bmax_with_eps + 1e-6)
    out["check_maxB0_le_Mq2"] = bool(B0max <= Mval * q ** 2 + 1e-6)
    out["B0_by_wt"] = {}
    for wv in sorted(set(r["wt"] for r in B0ratio)):
        rr = [r for r in B0ratio if r["wt"] == wv]
        out["B0_by_wt"][str(wv)] = dict(max_over_q2=max(r["B0_over_q2"] for r in rr),
                                        max_over_3mprime=max(r["B0_over_3mprime"] for r in rr))
    out["sec"] = round(time.time() - t0, 1)
    return out


if __name__ == "__main__":
    code, outp = sys.argv[1], sys.argv[2]
    ms = [int(x) for x in sys.argv[3:]]
    rng = np.random.default_rng(80702)
    res = []
    for m in ms:
        F = Field(m)
        q = F.q
        pinv = F.power(q - 2)
        cases = []
        for rho in (1, 0b111):
            K, eps = d0_K(F, rho)
            for hname in ("0", "a^3", "rand"):
                h = {"0": np.zeros(q, dtype=np.int64), "a^3": F.power(3), "rand": rng.integers(0, q, size=q)}[hname]
                cases.append((f"inv,d0(rho={rho}),h={hname}", PD(F, pinv, K, eps, h)))
        for j in range(2):
            K, eps = random_K(F, rng)
            cases.append((f"inv,randomK#{j},h=rand", PD(F, pinv, K, eps, rng.integers(0, q, size=q))))
        p3 = F.power(3)
        if is_apn_perm(F, p3):
            K, eps = d0_K(F, 1)
            cases.append(("x^3,d0,h=rand", PD(F, p3, K, eps, rng.integers(0, q, size=q))))
            K, eps = random_K(F, rng)
            cases.append(("x^3,randomK,h=rand", PD(F, p3, K, eps, rng.integers(0, q, size=q))))
        for name, P in cases:
            r = analyze(P, name, do_pairs=(m <= 5))
            print(json.dumps({k: v for k, v in r.items() if k not in ("B0_by_wt",)}), flush=True)
            res.append(r)
    json.dump(res, open(outp, "w"), indent=1)
    print("DONE")
