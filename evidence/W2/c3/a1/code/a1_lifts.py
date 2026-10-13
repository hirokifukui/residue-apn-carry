"""P3-08 (C3, Claude 2026-10-10): lifts and class-level constants for the A1 projected-sup recursion.
Extract p, h_nat, d from the C1 natural table (F(a,b) = (p(a), h(a) + d(a) b), code = a | b<<m),
build lifts h in {natural, h0, adversarialG(C1 table), random(seed 20261010), Gconc}, where Gconc is a
lift found by solving an F2-linear system so that ONE G row of T_B has an element exactly 1/q
(i.e. the C2 bound mu_G <= 1/q is attained on a G row).  Saves tables to c3/a1/data/.
usage: python3 -I a1_lifts.py
"""
import sys, os, json
import numpy as np
P = os.path.expanduser('~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher')
sys.path.insert(0, P + '/c1/code')
from codes import mk
from ringlib import GF2m

m = 5; q = 1 << m; N = q * q; mask = q - 1
add, neg, sub, J = mk(m)
MUL = GF2m(m).MUL
INV = np.zeros(q, dtype=np.int64)
for x in range(1, q):
    INV[x] = int(np.nonzero(MUL[x] == 1)[0][0])
X = np.arange(N); A = X & mask; Bh = X >> m
OUT = P + '/c3/a1'

def extract():
    base = np.load(P + '/c1/data/F_m5_r3.npy').astype(np.int64)
    p = base[np.arange(q)] & mask
    h = base[np.arange(q)] >> m
    d = (base[np.arange(q) | (1 << m)] >> m) ^ h
    assert np.array_equal(base >> m, h[A] ^ MUL[d[A], Bh])
    assert np.array_equal(base & mask, p[A])
    K = d ^ d[0]
    rho = [u for u in range(q) if K[u] == 0][1]
    return base, p, h, d, K, rho

def build(p, d, h):
    return p[A] | ((h[A] ^ MUL[d[A], Bh]) << m)

def mulmat(c):
    """5x5 F2 matrix of x -> c*x (column j = c * e_j)."""
    Mt = np.zeros((m, m), dtype=np.uint8)
    for j in range(m):
        y = int(MUL[c, 1 << j])
        for i in range(m):
            Mt[i, j] = (y >> i) & 1
    return Mt

def gf2_solve(Aeq, beq):
    """solve Aeq x = beq over F2; return one solution or None."""
    Aa = np.concatenate([Aeq % 2, (beq % 2)[:, None]], axis=1).astype(np.uint8)
    rows, cols = Aa.shape[0], Aa.shape[1] - 1
    piv = []; r = 0
    for c in range(cols):
        pr = None
        for i in range(r, rows):
            if Aa[i, c]:
                pr = i; break
        if pr is None: continue
        Aa[[r, pr]] = Aa[[pr, r]]
        for i in range(rows):
            if i != r and Aa[i, c]:
                Aa[i] ^= Aa[r]
        piv.append(c); r += 1
        if r == rows: break
    for i in range(r, rows):
        if Aa[i, :-1].sum() == 0 and Aa[i, -1]:
            return None
    x = np.zeros(cols, dtype=np.uint8)
    for i, c in enumerate(piv):
        x[c] = Aa[i, -1]
    return x

def gconc(p, d, K, rho, u, v, s):
    """Exact count of x with B(x+alpha)-B(x) = (s,t), alpha=(u,v) a G direction:
       each a gives exactly one b (K(u) != 0), and the condition is  t = D_u p(a) + (z0(a) & s).
       Bits outside s: (D_u p(a) xor t) & ~s == 0  -- independent of h; choose t_out maximising the set A.
       Bits inside s: F2-linear in h (and t_in).  Solve for ALL a in A simultaneously.
       Returns (h, t, |A|) or (None, None, |A|)."""
    nv = m * q + m
    Dp = np.array([int(p[a ^ u] ^ p[a]) for a in range(q)])
    outs = Dp & (mask ^ s)
    vals, cnts = np.unique(outs, return_counts=True)
    t_out = int(vals[np.argmax(cnts)]); Aset = [a for a in range(q) if outs[a] == t_out]
    rowsA = []; rowsb = []
    Kinv = int(INV[K[u]]); Mk = mulmat(Kinv)
    for a in Aset:
        au = a ^ u
        cb = int(MUL[Kinv, s ^ int(MUL[d[au], v ^ (a & u)])])
        MdMk = (mulmat(int(d[a])).astype(int) @ Mk.astype(int)) % 2
        coef = np.zeros((m, nv), dtype=np.uint8)
        coef[:, a * m:(a + 1) * m] ^= np.eye(m, dtype=np.uint8)
        coef[:, a * m:(a + 1) * m] ^= MdMk.astype(np.uint8)
        coef[:, au * m:(au + 1) * m] ^= MdMk.astype(np.uint8)
        const = int(MUL[d[a], cb])
        for i in range(m):
            if not (s >> i) & 1: continue
            row = coef[i].copy(); row[m * q + i] ^= 1
            rowsA.append(row); rowsb.append(((const >> i) ^ (int(Dp[a]) >> i)) & 1)
    sol = gf2_solve(np.array(rowsA), np.array(rowsb, dtype=np.uint8))
    if sol is None: return None, None, len(Aset)
    h = np.array([sum(int(sol[x * m + i]) << i for i in range(m)) for x in range(q)], dtype=np.int64)
    t_in = sum(int(sol[m * q + i]) << i for i in range(m)) & s
    return h, t_out | t_in, len(Aset)

def main():
    os.makedirs(OUT + '/data', exist_ok=True); os.makedirs(OUT + '/results', exist_ok=True)
    base, p, hn, d, K, rho = extract()
    info = {'m': m, 'rho': int(rho), 'gconc_search': []}
    found = None
    best = 0
    for sv in range(2, q):                       # s = 1 = rho is the E target
        for u in range(1, q):
            if u == rho: continue
            for v in (0, 3):
                h, t, nA = gconc(p, d, K, rho, u, v, sv)
                info['gconc_search'].append({'s': sv, 'u': u, 'v': v, 'A': nA, 'solvable': h is not None})
                if h is not None and nA > best:
                    best = nA; found = (u, v, h, t, sv)
    info['gconc_solvable_count'] = sum(r['solvable'] for r in info['gconc_search'])
    info['gconc_tried'] = len(info['gconc_search'])
    lifts = {'natural': hn, 'h0': np.zeros(q, dtype=np.int64)}
    adv = np.load(P + '/c1/data/F_m5_r3_adversarialG.npy').astype(np.int64)
    ha = adv[np.arange(q)] >> m
    assert np.array_equal(adv, build(p, d, ha)); lifts['adversarialG'] = ha
    info['gconc_search'] = [r for r in info['gconc_search'] if r['solvable']]
    lifts['random'] = np.random.default_rng(20261010).integers(0, q, q)
    if found:
        u, v, h, t, sv = found
        lifts['Gconc'] = h
        F = build(p, d, h); Bm = J(F)
        alpha = u | (v << m); delta = sv | (t << m)
        cnt = int(np.sum(sub(Bm[add(X, alpha)], Bm) == delta))
        info['gconc'] = {'s': sv, 'u': u, 'v': v, 'alpha_code': int(alpha), 'delta_code': int(delta), 'count': cnt,
                         'equals_q': cnt == q}
        print('Gconc: alpha', alpha, 'delta', delta, 'count', cnt, '(q =', q, ')')
    for name, h in lifts.items():
        F = build(p, d, h)
        assert len(set(F.tolist())) == N
        np.save(OUT + '/data/F_%s.npy' % name, F)
        info.setdefault('lifts', []).append(name)
    json.dump(info, open(OUT + '/results/a1_lifts.json', 'w'), indent=1)
    print('lifts', list(lifts)); print('A1_LIFTS=PASS')

if __name__ == '__main__':
    main()
