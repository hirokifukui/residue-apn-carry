"""P7-03 finite calibration: linear certificate (three top coefficients of Phi), Psi=Phi^2,
nonzero-count bound, exact-degree dichotomy, F-linearity of ell."""
import sys, os, json, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gd_lib import (GF, dset, derive, AB, Phi_poly, Psi_all, peval, pdeg, rand_lin,
                    lin_table, parity)

rng = random.Random(20261012703)
out = {"task": "P7-03", "per_m": {}, "first_failures": []}


def fail(rec):
    if len(out["first_failures"]) < 20:
        out["first_failures"].append(rec)


for m in (3, 4, 5):
    F = GF(m)
    q = F.q
    s = q // 2 - 1
    st = {"key_checks": 0, "coef_s_ok": 0, "coef_s1_ok": 0, "coef_s2_ok": 0, "psi_eq_phi2": 0,
          "ell_nonzero_cases": 0, "bound_ok": 0, "deg_s1_cases": 0, "deg_s2_cases": 0,
          "deg_ok": 0, "min_nonzero_deg_s1": q, "min_nonzero_deg_s2": q,
          "ell0_cases": 0, "ell0_min_nonzero": q, "ell0_max_deg": -1,
          "linearity_trials": 0, "linearity_ok": 0, "exhaustive_m3_keys": 0, "exhaustive_m3_ok": 0}
    for D in dset(m, F):
        d, rho = D["d"], D["rho"]
        Dv = derive(F, D)
        eta, beta, r = Dv["eta"], Dv["beta"], Dv["r"]
        chi_mask = rho & -rho  # chi(a)=bit of lowest nonzero coordinate of rho
        g = [r[a] if parity(a & chi_mask) else 0 for a in range(q)]
        hs = []
        hs.append(("rand1", [rng.randrange(q) for _ in range(q)]))
        hs.append(("rand2", [rng.randrange(q) for _ in range(q)]))
        hs.append(("cube", [F.pow(a, 3) for a in range(q)]))
        h0 = [rng.randrange(q) for _ in range(q)]
        l0 = AB(F, D, Dv, h0)[2]
        hs.append(("rand_repaired_ell0", [h0[a] ^ F.mul(l0, g[a]) for a in range(q)]))
        Al = rand_lin(F, rng)
        off = rng.randrange(q)
        hs.append(("affine", [Al[a] ^ off for a in range(q)]))
        hs.append(("g_d", g))
        for hn, h in hs:
            A, B, ell = AB(F, D, Dv, h)
            if hn == "rand_repaired_ell0" and ell != 0:
                fail({"m": m, "d": D["name"], "h": hn, "what": "repair did not give ell=0"})
            Ls = [("randL%d" % k, rand_lin(F, rng)) for k in range(3)]
            # L with tau = eta*A (degree-drop case), built from a random L0 and functional chi
            L0 = rand_lin(F, rng)
            tgt = F.mul(eta, A)
            corr = tgt ^ L0[rho]
            Ls.append(("tau_eq_etaA", [L0[a] ^ (corr if parity(a & chi_mask) else 0) for a in range(q)]))
            for Ln, Lt in Ls:
                mu = rng.randrange(q)
                tau = Lt[rho]
                if Ln == "tau_eq_etaA":
                    assert tau == tgt
                P = Phi_poly(F, d, h, Lt, mu)
                st["key_checks"] += 1
                e1 = F.mul(F.pow(beta, s - 1), A ^ F.mul(beta, tau))
                e2 = F.mul(F.pow(beta, s - 2), B ^ F.mul(F.sq[beta], F.sq[tau]))
                ok0, ok1, ok2 = P[s] == 0, P[s - 1] == e1, P[s - 2] == e2
                st["coef_s_ok"] += ok0
                st["coef_s1_ok"] += ok1
                st["coef_s2_ok"] += ok2
                if not (ok0 and ok1 and ok2):
                    first = "C^s" if not ok0 else ("C^(s-1)" if not ok1 else "C^(s-2)")
                    fail({"m": m, "d": D["name"], "h": hn, "L": Ln, "mu": mu, "first_bad": first,
                          "got": P[s - 2:], "exp": [e2, e1, 0]})
                ps = Psi_all(F, d, h, Lt, mu)
                okp = all(ps[c] == F.sq[peval(F, P, c)] for c in range(q))
                st["psi_eq_phi2"] += okp
                if not okp:
                    fail({"m": m, "d": D["name"], "h": hn, "L": Ln, "what": "Psi != Phi^2"})
                nz = sum(1 for v in ps if v)
                dg = pdeg(P)
                if ell:
                    st["ell_nonzero_cases"] += 1
                    b = nz >= q // 2 + 2
                    st["bound_ok"] += b
                    if not b:
                        fail({"m": m, "d": D["name"], "h": hn, "L": Ln, "what": "bound", "nz": nz})
                    if tau == F.mul(eta, A):
                        st["deg_s2_cases"] += 1
                        okd = dg == q // 2 - 3 and nz >= q // 2 + 3
                        st["min_nonzero_deg_s2"] = min(st["min_nonzero_deg_s2"], nz)
                    else:
                        st["deg_s1_cases"] += 1
                        okd = dg == q // 2 - 2
                        st["min_nonzero_deg_s1"] = min(st["min_nonzero_deg_s1"], nz)
                    st["deg_ok"] += okd
                    if not okd:
                        fail({"m": m, "d": D["name"], "h": hn, "L": Ln, "what": "degree", "deg": dg})
                else:
                    st["ell0_cases"] += 1
                    st["ell0_min_nonzero"] = min(st["ell0_min_nonzero"], nz)
                    st["ell0_max_deg"] = max(st["ell0_max_deg"], dg)
        # F-linearity of ell
        for _ in range(40):
            h1 = [rng.randrange(q) for _ in range(q)]
            h2 = [rng.randrange(q) for _ in range(q)]
            al = rng.randrange(q)
            hc = [F.mul(al, h1[a]) ^ h2[a] for a in range(q)]
            okl = AB(F, D, Dv, hc)[2] == F.mul(al, AB(F, D, Dv, h1)[2]) ^ AB(F, D, Dv, h2)[2]
            st["linearity_trials"] += 1
            st["linearity_ok"] += okl
            if not okl:
                fail({"m": m, "d": D["name"], "what": "ell linearity"})
        # m=3: exhaustive over ALL F2-linear L (q^m) and all mu, for two h with ell!=0
        if m == 3:
            cnt = 0
            for hn, h in (("rand1", hs[0][1]), ("g_d", g)):
                if AB(F, D, Dv, h)[2] == 0:
                    continue
                for cols_code in range(q ** m):
                    cols = [(cols_code // q ** i) % q for i in range(m)]
                    Lt = lin_table(q, cols)
                    for mu in range(q):
                        ps = Psi_all(F, d, h, Lt, mu)
                        nz = sum(1 for v in ps if v)
                        st["exhaustive_m3_keys"] += 1
                        if nz >= q // 2 + 2:
                            st["exhaustive_m3_ok"] += 1
                        else:
                            fail({"m": 3, "d": D["name"], "h": hn, "what": "exhaustive bound", "cols": cols, "mu": mu})
    out["per_m"][str(m)] = st
    print(m, json.dumps(st))
out["PASS"] = not out["first_failures"]
json.dump(out, open(sys.argv[1], "w"), indent=1)
print("PASS", out["PASS"], "failures", out["first_failures"][:3])
