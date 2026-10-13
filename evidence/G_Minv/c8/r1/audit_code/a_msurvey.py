# Exact M(p,d) for p = inverse, several K, odd m=3..11; compare with Prop I bound 2^{e+1}+2.
import sys, json, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from acore import GF, M_count, linK_from_coeffs, popc

out = sys.argv[1]
rng = np.random.default_rng(20261012)
res = []
for m in (3, 5, 7, 9, 11):
    F = GF(m); q = F.q
    x = np.arange(q)
    p = F.inv(x)
    # APN + perm sanity for inverse (m odd)
    assert len(set(p.tolist())) == q
    cases = []
    # d0-type: K = K0(x/rho), K0 = x^4+x^2 (e=2); rho of weight 1,2,3, plus random rho
    rhos = [1, 0b11, 0b111, 0b1011 if m >= 4 else 0b101, int(rng.integers(2, q))]
    for rho in rhos:
        ir = int(F.inv(rho))
        K = linK_from_coeffs(F, [0, int(F.pw(ir, 2)), int(F.pw(ir, 4))])
        cases.append(("K0(x/rho)", rho, 2, K))
    # higher 2-degree, kernel {0,rho}: K = K0(x/rho)^{2^{e-2}}  -> 2-degree e
    for e in (3, 4, 5):
        if e < m:
            for rho in (1, 0b111):
                ir = int(F.inv(rho))
                K0 = linK_from_coeffs(F, [0, int(F.pw(ir, 2)), int(F.pw(ir, 4))])
                K = F.pw(K0, 1 << (e - 2))
                cases.append((f"K0(x/rho)^(2^{e-2})", rho, e, K))
    # x^{2^e} + c x  type with kernel dim 1: K(x)=x^{2^e}+x*r^{2^e-1} -> kernel {0,r}*F_{2^gcd}; need gcd(e,m)=1
    for e in (1, 2, 3, 4):
        if np.gcd(e, m) == 1 and e < m:
            r = int(rng.integers(2, q))
            K = F.pw(x, 1 << e) ^ F.mul(x, np.full(q, int(F.pw(r, (1 << e) - 1))))
            cases.append((f"x^(2^{e})+r^(2^{e}-1)x", r, e, K))
    # random F2-linear K with 1-dim kernel (2-degree generically m-1)
    for t in range(3):
        while True:
            Mx = rng.integers(0, 2, size=(m, m))
            # rank m-1 over F2
            A = Mx.copy() % 2; rank = 0
            for c in range(m):
                piv = [r for r in range(rank, m) if A[r, c]]
                if not piv: continue
                A[[rank, piv[0]]] = A[[piv[0], rank]]
                for r in range(m):
                    if r != rank and A[r, c]: A[r] ^= A[rank]
                rank += 1
            if rank == m - 1: break
        cols = [int(sum(int(Mx[i, j]) << i for i in range(m))) for j in range(m)]
        K = np.array([np.bitwise_xor.reduce([cols[j] for j in range(m) if xx >> j & 1] or [0]) for xx in range(q)])
        cases.append(("randomlinear", None, m - 1, K))
    for name, rho_given, e, K in cases:
        ker = [int(t) for t in x if K[t] == 0]
        if len(ker) != 2:
            res.append(dict(m=m, K=name, skip="kernel dim != 1", ker=len(ker))); continue
        rho = ker[1]
        im = set(K.tolist())
        eps_list = [int(t) for t in x if int(t) not in im]
        # epsilon: 1 if allowed, plus one random allowed
        epss = ([1] if 1 not in im else []) + [eps_list[int(rng.integers(len(eps_list)))]]
        for eps in epss:
            d = eps ^ K
            M = M_count(F, p, d, K, rho)
            bound = 2 ** (e + 1) + 2
            res.append(dict(m=m, K=name, rho=rho, wt_rho=int(popc(rho)), e=e, eps=eps, M=M,
                            propI_bound=bound, ok=M <= bound))
            print(m, name, "rho", rho, "wt", int(popc(rho)), "e", e, "eps", eps, "M", M, "bound", bound,
                  "OK" if M <= bound else "VIOLATION", flush=True)
json.dump(res, open(out, "w"), indent=1)
print("violations:", sum(1 for r in res if r.get("ok") is False))
