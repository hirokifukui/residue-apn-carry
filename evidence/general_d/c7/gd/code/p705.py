"""P7-05 finite calibration: gate-DAG evaluation circuit of g_d (m=5), AND count,
lambda*g as F2-linear matrix (no AND), and limited local Psi==0 control (pre vs post repair)."""
import sys, os, json, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gd_lib import GF, dset, derive, AB, Psi_all, parity

rng = random.Random(20261012705)
m = 5
F = GF(m)
q = F.q
out = {"task": "P7-05", "m": m, "circuits": [], "local_control": [], "fail": []}


class DAG:
    def __init__(self, n):
        self.g = [("IN", i) for i in range(n)]
        self.g.append(("CONST", 0))
        self.g.append(("CONST", 1))
        self.C0, self.C1 = n, n + 1

    def add(self, op, x, y):
        self.g.append((op, x, y))
        return len(self.g) - 1

    def xor_of(self, nodes):
        if not nodes:
            return self.C0
        cur = nodes[0]
        for nd in nodes[1:]:
            cur = self.add("XOR", cur, nd)
        return cur

    def eval(self, a, outs):
        v = []
        for gt in self.g:
            if gt[0] == "IN":
                v.append(a >> gt[1] & 1)
            elif gt[0] == "CONST":
                v.append(gt[1])
            elif gt[0] == "XOR":
                v.append(v[gt[1]] ^ v[gt[2]])
            else:
                v.append(v[gt[1]] & v[gt[2]])
        return sum(v[o] << j for j, o in enumerate(outs))

    def count(self, op):
        return sum(1 for gt in self.g if gt[0] == op)


ds = {D["name"]: D for D in dset(m, F)}
chosen = ["m5_rho2_r", "m5_rho22_r"]
for name in chosen:
    D = ds[name]
    rho = D["rho"]
    assert name != "m5_d0"
    Dv = derive(F, D)
    r = Dv["r"]
    chi = rho & -rho
    gref = [r[a] if parity(a & chi) else 0 for a in range(q)]
    # r is F2-affine: r(a)=r0 + sum a_i R_i ; verify on all points
    r0 = r[0]
    R = [r[1 << i] ^ r0 for i in range(m)]
    aff = all(r[a] == r0 ^ (0 if a == 0 else __import__("functools").reduce(lambda x, y: x ^ y, [R[i] for i in range(m) if a >> i & 1], 0)) for a in range(q))
    dag = DAG(m)
    chi_node = dag.xor_of([i for i in range(m) if chi >> i & 1])
    outs = []
    for j in range(m):
        terms = [i for i in range(m) if R[i] >> j & 1]
        cst = r0 >> j & 1
        if not terms:
            outs.append(chi_node if cst else dag.C0)
            continue
        node = dag.xor_of(terms)
        if cst:
            node = dag.add("XOR", node, dag.C1)
        outs.append(dag.add("AND", chi_node, node))
    n_and = dag.count("AND")
    table_ok = all(dag.eval(a, outs) == gref[a] for a in range(q))
    # lambda*g via F2 matrix of multiplication by lambda
    lam = rng.randrange(2, q)
    Mcols = [F.mul(lam, 1 << i) for i in range(m)]
    Mrows = [[(Mcols[i] >> j) & 1 for i in range(m)] for j in range(m)]  # row j, col i
    mat_ok = all(F.mul(lam, x) == __import__("functools").reduce(lambda u, v: u ^ v, [Mcols[i] for i in range(m) if x >> i & 1], 0) for x in range(q))
    lam_outs = [dag.xor_of([outs[i] for i in range(m) if Mrows[j][i]]) for j in range(m)]
    n_and_after = dag.count("AND")
    lam_ok = all(dag.eval(a, lam_outs) == F.mul(lam, gref[a]) for a in range(q))
    all_lam_mat_ok = all(
        all(F.mul(L, x) == __import__("functools").reduce(lambda u, v: u ^ v, [F.mul(L, 1 << i) for i in range(m) if x >> i & 1], 0) for x in range(q))
        for L in range(q))
    rec = {"d": name, "rho": rho, "wt_rho": bin(rho).count("1"), "eta": Dv["eta"], "chi_mask": chi,
           "r_affine": aff, "r0": r0, "R_cols": R, "gates": dag.g, "outputs": outs,
           "n_AND": n_and, "n_XOR": dag.count("XOR") , "AND_le_m": n_and <= m,
           "table_match_32": table_ok, "lambda": lam, "M_lambda_rows": Mrows, "M_lambda_ok": mat_ok,
           "lambda_outputs": lam_outs, "n_AND_after_lambda": n_and_after,
           "lambda_g_match_32": lam_ok, "mult_by_any_lambda_is_F2_linear_matrix": all_lam_mat_ok}
    for k in ("r_affine", "AND_le_m", "table_match_32", "M_lambda_ok", "lambda_g_match_32",
              "mult_by_any_lambda_is_F2_linear_matrix"):
        if not rec[k]:
            out["fail"].append((name, k))
    if n_and_after != n_and:
        out["fail"].append((name, "lambda added AND"))
    out["circuits"].append(rec)
    print(name, "wt", rec["wt_rho"], "AND", n_and, "XOR", rec["n_XOR"], "match", table_ok, "lam", lam, lam_ok, "AND after", n_and_after)

# limited local control: same d, same (L,mu) grid L(u)=u AND kappa (componentwise), 32 kappa x 32 mu
def zero_count(D, h):
    d = D["d"]
    z = 0
    for kappa in range(q):
        Lt = [u & kappa for u in range(q)]
        for mu in range(q):
            if not any(Psi_all(F, d, h, Lt, mu)):
                z += 1
    return z

cases = []
for name in chosen:
    D = ds[name]
    Dv = derive(F, D)
    chi = D["rho"] & -D["rho"]
    g = [Dv["r"][a] if parity(a & chi) else 0 for a in range(q)]
    h = [rng.randrange(q) for _ in range(q)]
    lh = AB(F, D, Dv, h)[2]
    hpre = [h[a] ^ F.mul(lh, g[a]) for a in range(q)]
    cases.append((name, "rand_ell0", D, Dv, hpre, g))
    cube = [F.pow(a, 3) for a in range(q)]
    lc = AB(F, D, Dv, cube)[2]
    cases.append((name, "cube_ell0", D, Dv, [cube[a] ^ F.mul(lc, g[a]) for a in range(q)], g))
# C6 special d0 with h=a^21 (X21 family)
D = ds["m5_d0"]
Dv = derive(F, D)
g = [Dv["r"][a] if parity(a & 1) else 0 for a in range(q)]
cases.append(("m5_d0", "a^21", D, Dv, [F.pow(a, 21) for a in range(q)], g))
for name, hn, D, Dv, hpre, g in cases:
    hpost = [hpre[a] ^ g[a] for a in range(q)]
    lpre, lpost = AB(F, D, Dv, hpre)[2], AB(F, D, Dv, hpost)[2]
    zpre, zpost = zero_count(D, hpre), zero_count(D, hpost)
    rec = {"d": name, "h_pre": hn, "ell_pre": lpre, "ell_post": lpost, "grid": "kappa 32 x mu 32 = 1024",
           "Psi_identically_zero_pre": zpre, "Psi_identically_zero_post": zpost}
    if lpost != 0 and zpost != 0:
        out["fail"].append((name, hn, "post repair has Psi==0"))
    out["local_control"].append(rec)
    print(rec)
out["PASS"] = not out["fail"]
json.dump(out, open(sys.argv[1], "w"), indent=1)
print("PASS", out["PASS"], out["fail"])
