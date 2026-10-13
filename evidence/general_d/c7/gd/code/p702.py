"""P7-02 finite calibration: normalisation of general affine d."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gd_lib import GF, MODSTR, dset, derive, check_K, parity

out = {"task": "P7-02", "per_m": {}, "fail": []}
for m in (3, 4, 5):
    F = GF(m)
    q = F.q
    H = sorted(z for z in range(q) if F.tr(z) == 1)
    rows = []
    for D in dset(m, F):
        d, rho, K = D["d"], D["rho"], D["K"]
        lin, ker = check_K(F, K, rho)
        ImK = set(K)
        rec = {"name": D["name"], "rho": rho, "wt_rho": bin(rho).count("1"), "eps": D["eps"],
               "K_linear": lin, "kerK": ker, "dimImK_hyperplane": len(ImK) == q // 2,
               "eps_notin_ImK": D["eps"] not in ImK}
        Dv = derive(F, D)
        rec["eta_candidates"] = Dv["etas"]
        rec["eta_unique"] = len(Dv["etas"]) == 1
        if rec["eta_unique"]:
            eta, beta, r = Dv["eta"], Dv["beta"], Dv["r"]
            rec["eta"], rec["beta"] = eta, beta
            # Im d is exactly the affine hyperplane {Tr(eta z)=1}
            rec["Imd_eq_trace_hyperplane"] = Dv["Imd"] == sorted(z for z in range(q) if F.tr(F.mul(eta, z)) == 1)
            rec["d_eq_beta_r2"] = all(d[a] == F.mul(beta, F.sq[r[a]]) for a in range(q))
            rec["r_image_eq_H"] = sorted(set(r)) == H
            fib_ok = True
            for t in H:
                pre = sorted(a for a in range(q) if r[a] == t)
                if len(pre) != 2 or pre[0] ^ pre[1] != rho:
                    fib_ok = False
            rec["fibres_are_a_a_plus_rho"] = fib_ok
            rec["r_rho_invariant"] = all(r[a] == r[a ^ rho] for a in range(q))
            rec["sum_H_rinv"] = 0
            for t in H:
                rec["sum_H_rinv"] ^= F.inv[t]
            if D["name"] == "m5_d0":
                rec["d0_eta_is_1"] = eta == 1
                rec["d0_r_eq_a2+a+1"] = all(r[a] == F.sq[a] ^ a ^ 1 for a in range(q))
                rec["d0_eps"] = D["eps"]
        oks = [v for k, v in rec.items() if isinstance(v, bool)]
        rec["ALL_OK"] = all(oks)
        if not rec["ALL_OK"]:
            out["fail"].append(rec["name"])
        rec["d_table"] = d
        rows.append(rec)
    out["per_m"][str(m)] = {"modulus": MODSTR[m], "H_size": len(H), "n_d": len(rows), "d": rows}
out["PASS"] = not out["fail"]
json.dump(out, open(sys.argv[1], "w"), indent=1)
for m, v in out["per_m"].items():
    print(m, v["modulus"], "n_d", v["n_d"], [(r["name"], r.get("eta"), r.get("beta"), r["ALL_OK"]) for r in v["d"]])
print("PASS", out["PASS"], "fail", out["fail"])
