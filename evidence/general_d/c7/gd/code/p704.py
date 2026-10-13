"""P7-04 finite calibration: quadratic repair g_d = chi * r."""
import sys, os, json, random
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gd_lib import GF, dset, derive, AB, Psi_all, rand_lin, coord_degs, parity

rng = random.Random(20261012704)
out = {"task": "P7-04", "per_m": {}, "fail": []}


def rank_Fq(F, rows):
    M = [list(r) for r in rows]
    rk = 0
    ncol = len(M[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = F.inv[M[rk][c]]
        M[rk] = [F.mul(iv, x) for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [x ^ F.mul(f, y) for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk


for m in (3, 4, 5):
    F = GF(m)
    q = F.q
    zeroL = [0] * q
    st = {"d": []}
    monos = [0] + [1 << i for i in range(m)] + [(1 << i) | (1 << j) for i in range(m) for j in range(i + 1, m)]
    D_expected = 1 + m + comb(m, 2)
    # evaluation vectors of Boolean monomials (x_S(a)=1 iff S subset of a) as F-valued functions
    rows = [[1 if (a & S) == S else 0 for a in range(q)] for S in monos]
    st["Q2_dim_expected"] = D_expected
    st["Q2_rank_over_Fq"] = rank_Fq(F, rows)
    st["Q2_count_argument"] = "each of m coordinates: 2^D Boolean fns of deg<=2 -> 2^(mD)=q^D = |Fq-span|"
    if st["Q2_rank_over_Fq"] != D_expected:
        out["fail"].append((m, "Q2 rank"))
    for D in dset(m, F):
        d, rho = D["d"], D["rho"]
        Dv = derive(F, D)
        r = Dv["r"]
        chi1 = rho & -rho
        cands = [c for c in range(1, q) if parity(c & rho) and c != chi1]
        chi2 = rng.choice(cands)
        rec = {"name": D["name"], "rho": rho, "chi_masks": [chi1, chi2], "per_chi": []}
        for chi in (chi1, chi2):
            g = [r[a] if parity(a & chi) else 0 for a in range(q)]
            cd = coord_degs(F, g)
            A, B, ell = AB(F, D, Dv, g)
            dg_ok = max(cd) == 2
            # Delta g = r on every pair
            dl = all(g[a] ^ g[a ^ rho] == r[a] for a in range(q))
            # repair examples
            rep = []
            for _ in range(3):
                h = [rng.randrange(q) for _ in range(q)]
                lh = AB(F, D, Dv, h)[2]
                h0 = [h[a] ^ F.mul(lh, g[a]) for a in range(q)]
                l0 = AB(F, D, Dv, h0)[2]
                l1 = AB(F, D, Dv, [h0[a] ^ g[a] for a in range(q)])[2]
                rep.append([lh, l0, l1])
            rep_ok = all(x[1] == 0 and x[2] == 1 for x in rep)
            # all lambda: ell(h+lam g)=ell(h)+lam
            h = [rng.randrange(q) for _ in range(q)]
            lh = AB(F, D, Dv, h)[2]
            lam_ok = all(AB(F, D, Dv, [h[a] ^ F.mul(lam, g[a]) for a in range(q)])[2] == lh ^ lam for lam in range(q))
            pc = {"chi": chi, "coord_degs": cd, "deg_exactly_2": dg_ok, "Delta_g_eq_r": dl,
                  "A": A, "B": B, "ell": ell, "ABell_ok": (A, B, ell) == (1, 0, 1),
                  "repair_examples[ell(h),ell(h0),ell(h0+g)]": rep, "repair_ok": rep_ok,
                  "all_lambda_ok": lam_ok}
            if not (dg_ok and dl and pc["ABell_ok"] and rep_ok and lam_ok):
                out["fail"].append((m, D["name"], chi))
            rec["per_chi"].append(pc)
        # affine h with L=0: Psi == 0 for all c and all mu
        n_aff = 40 if m in (3, 4) else 10
        aff_ok = 0
        aff_ell0 = 0
        for _ in range(n_aff):
            Al = rand_lin(F, rng)
            off = rng.randrange(q)
            h = [Al[a] ^ off for a in range(q)]
            aff_ell0 += AB(F, D, Dv, h)[2] == 0
            ok = all(not any(Psi_all(F, d, h, zeroL, mu)) for mu in range(q))
            aff_ok += ok
        rec["affine_tests"] = n_aff
        rec["affine_Psi_zero_all_c_all_mu"] = aff_ok
        rec["affine_ell_zero"] = aff_ell0
        if aff_ok != n_aff or aff_ell0 != n_aff:
            out["fail"].append((m, D["name"], "affine"))
        st["d"].append(rec)
    # m=3 reference: pass rate of ell != 0 over random Q2 samples (per d)
    if m == 3:
        pr = []
        for D in dset(m, F):
            Dv = derive(F, D)
            N = 20000
            npass = 0
            for _ in range(N):
                co = [rng.randrange(q) for _ in monos]
                h = [0] * q
                for c, S in zip(co, monos):
                    if c:
                        for a in range(q):
                            if (a & S) == S:
                                h[a] ^= c
                npass += AB(F, D, Dv, h)[2] != 0
            pr.append({"d": D["name"], "N": N, "pass": npass, "rate": npass / N, "1-1/q": 1 - 1 / q})
        st["Q2_pass_rate_reference"] = pr
    out["per_m"][str(m)] = st
    print(m, "Q2 rank", st["Q2_rank_over_Fq"], "D", D_expected,
          [(x["name"], [p["coord_degs"] for p in x["per_chi"]], x["affine_Psi_zero_all_c_all_mu"]) for x in st["d"]])
    if m == 3:
        print([(p["d"], p["pass"], round(p["rate"], 4)) for p in st["Q2_pass_rate_reference"]])
out["PASS"] = not out["fail"]
json.dump(out, open(sys.argv[1], "w"), indent=1)
print("PASS", out["PASS"], out["fail"][:5])
