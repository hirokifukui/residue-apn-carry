"""Task (1): formula G vs brute DDT->Walsh, m=3,5, several PD tables. Writes results/t1_verify.json"""
import sys, json, time
import numpy as np
sys.path.insert(0, sys.argv[1])
from gcore import Field, PD, d0_K, random_K, brute_ddt, brute_G, formula_G, is_apn_perm

out = []
rng = np.random.default_rng(807)
for m in (3, 5):
    F = Field(m)
    q = F.q
    pinv = F.power(q - 2)
    assert is_apn_perm(F, pinv)
    tables = []
    for rho in (1, 0b111):
        K, eps = d0_K(F, rho)
        for hname in ("0", "a^3", "rand"):
            h = {"0": np.zeros(q, dtype=np.int64), "a^3": F.power(3),
                 "rand": rng.integers(0, q, size=q)}[hname]
            tables.append((f"inv,d0(rho={rho}),h={hname}", PD(F, pinv, K, eps, h)))
    K, eps = random_K(F, rng)
    tables.append(("inv,randomK,h=rand", PD(F, pinv, K, eps, rng.integers(0, q, size=q))))
    if m == 5:
        p3 = F.power(3)
        assert is_apn_perm(F, p3)
        K, eps = d0_K(F, 1)
        tables.append(("x^3,d0,h=rand", PD(F, p3, K, eps, rng.integers(0, q, size=q))))
    for name, P in tables:
        t0 = time.time()
        D = brute_ddt(P)
        gb = brute_G(P, D)
        gf = formula_G(P)
        ok = bool(np.array_equal(gb, gf))
        vals = sorted(set(np.unique(gf).tolist()))
        out.append(dict(m=m, table=name, rho=P.rho, entries_equal=ok, nentries=int(gf.size),
                        value_set=vals, sec=round(time.time() - t0, 2)))
        print(out[-1], flush=True)
json.dump(out, open(sys.argv[2], "w"), indent=1)
assert all(o["entries_equal"] for o in out)
print("ALL_EQUAL")
