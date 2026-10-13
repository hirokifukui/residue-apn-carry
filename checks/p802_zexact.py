"""p802_zexact.py -- P8-02 independent check (C8, Claude). Usage: python3 -I -B p802_zexact.py OUT.json
For m in (3, 5) and several admissible d (d0 and d = 1 + K0(x/rho)), p = inverse, h in {0, a^3, random}:
 (1) exact integer identity: q^2-scaled Walsh of the physical Z block equals the column x_s
     (x_s(nu) = q^-2 * sum_v (-1)^<nu,v> w_s(v), w_s(v) = 2*[s/v in Im d]) repeated n_s = 2^(m-wt s)-1 times;
 (2) exact integer Gram: sum_{nu != 0} W_s(nu) W_t(nu) = q^2 [s = t] (W = q^2 x_s);
 (3) the physical norm ||M_Z||^2 (SVD of P_out T'^T P_in on the u = 0 input fibre, P = fibrewise centring on W)
     compared with (q/2-1)/q^2, and the exact Rayleigh quotient of the physical vector built from x_s - x_t
     (wt s = wt t = 1) as a rational number.
Finite calibration only; the general statement is the paper proof (NEW_DERIVATIONS A, re-proved in RESPONSE_C8).
"""
import sys, json, random
from fractions import Fraction
import numpy as np
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from grlib import GF, d0_table, ddt_B, popcount, dot


def d_rho(K, rho):
    """d(a) = 1 + K0(a/rho), K0(x) = x^4 + x^2; ker = {0, rho}; Im d = {Tr = 1} for odd m."""
    q = K.q
    ir = int(K.inv[rho])
    out = []
    for a in range(q):
        x = int(K.mul[a, ir])
        x2 = int(K.mul[x, x])
        out.append(1 ^ x2 ^ int(K.mul[x2, x2]))
    return np.array(out, dtype=np.int64)


def run_case(K, d, h, label):
    q, m = K.q, K.m
    N = q * q
    p = K.inv.copy()
    D = ddt_B(K, p, d, h)
    T = D.astype(float) / N
    imd = set(int(x) for x in d)
    # (1) Walsh of the Z rows: rows alpha = (0, v), v != 0 ; columns (s, t)
    H = np.array([[(-1) ** dot(i, j) for j in range(q)] for i in range(q)], dtype=np.int64)
    ok1 = True
    W = {}
    for s in range(1, q):
        w = np.array([0] + [2 if int(K.mul[s, int(K.inv[v])]) in imd else 0 for v in range(1, q)], dtype=np.int64)
        W[s] = H @ w  # q^2 x_s(nu) for every nu (nu = 0 included)
    for s in range(1, q):
        for xi in range(1, q):
            # integer q^2 * hatT((0,eta),(s,xi)) = q * sum_{v,t} (-1)^{<eta,v>+<xi,t>} D((0,v),(s,t)) / N * q^2 / q
            col = np.zeros(q, dtype=np.int64)
            for v in range(q):
                row = D[0 + q * v]
                acc = 0
                for t in range(q):
                    c = row[s + q * t]
                    if c:
                        acc += (-1) ** dot(xi, t) * c
                col += H[:, v] * acc
            # col = sum_v (-1)^{<eta,v>} sum_t ..., hatT = col/(q*N) ; q^2 hatT = col/q
            expect = W[s] if (s & xi) == 0 else np.zeros(q, dtype=np.int64)
            if not np.array_equal(col[1:] * 1, expect[1:] * q):  # col/q == expect  <=> col == q*expect
                ok1 = False
    # (2) exact Gram
    gram_ok = True
    for s in range(1, q):
        for t in range(1, q):
            g = int(np.dot(W[s][1:], W[t][1:]))
            if g != (q * q if s == t else 0):
                gram_ok = False
    sums = sorted(set(Fraction(int(W[s][1:].sum()), q * q) for s in W))  # = q^2 * sum_{nu!=0} x_s(nu) / q^2
    # (3) physical norm
    Wst = list(range(1, N))
    pos = {x: i for i, x in enumerate(Wst)}
    Tp = T[1:, 1:]  # rows/cols = W (state 0 removed); index i -> state i+1
    lo = np.array([x % q for x in Wst])

    def centring():
        P = np.eye(N - 1)
        for s in range(q):
            idxs = np.nonzero(lo == s)[0]
            P[np.ix_(idxs, idxs)] -= 1.0 / len(idxs)
        return P
    P = centring()
    inZ = np.nonzero(lo == 0)[0]
    X = P @ Tp.T @ P[:, inZ]
    sv = np.linalg.svd(X, compute_uv=False)
    phys = float(sv[0] ** 2)
    target = (q / 2 - 1) / q ** 2
    # exact Rayleigh quotient of the physical witness: input f on u=0 fibre (v != 0) with Walsh coeffs from x_s - x_t
    s1, t1 = 1, 2
    # input function f(v) = sum_nu c(nu) (-1)^{<nu,v>}, c = x_s - x_t on nu != 0, c(0) = 0; f(0) must vanish:
    c = np.zeros(q, dtype=np.int64)
    c[1:] = W[s1][1:] - W[t1][1:]
    f = H @ c  # q^2 * q * (function values) up to scale
    f0 = int(f[0])
    # physical vector on W: states (0, v), v != 0 -> index pos[q*v]
    vec = np.zeros(N - 1)
    for v in range(1, q):
        vec[pos[q * v]] = f[v]
    vec_c = P @ vec
    img = P @ Tp.T @ vec_c
    # exact rational Rayleigh quotient using integer DDT: (T^T vec)(beta) = sum_alpha D[alpha,beta] vec(alpha) / N
    fv = {q * v: int(f[v]) for v in range(1, q)}
    mean_in = Fraction(sum(fv.values()), q - 1)
    fin = {k: Fraction(val) - mean_in for k, val in fv.items()}
    img_ex = {}
    for k, val in fin.items():
        row = D[k]
        for b in np.nonzero(row)[0]:
            img_ex[int(b)] = img_ex.get(int(b), Fraction(0)) + Fraction(int(row[b]), N) * val
    # centre output on W fibres
    num = Fraction(0)
    for s in range(q):
        members = [x for x in range(1, N) if x % q == s]
        vals = [img_ex.get(x, Fraction(0)) for x in members]
        mu = sum(vals, Fraction(0)) / len(members)
        num += sum(((v - mu) ** 2 for v in vals), Fraction(0))
    den = sum((v ** 2 for v in fin.values()), Fraction(0))
    rq = num / den
    return {
        'label': label, 'm': m, 'walsh_formula_ok': bool(ok1), 'gram_exact_ok': bool(gram_ok),
        'sum_nu_nonzero_x_s_times_q': [str(x) for x in sums],
        'f0_of_witness': f0, 'phys_norm2': phys, 'target_(q/2-1)/q^2': target,
        'phys_minus_target': phys - target,
        'witness_rayleigh_exact': str(rq), 'witness_equals_target': rq == Fraction(q // 2 - 1, q * q),
    }


def main(out):
    random.seed(8202)
    res = []
    for m in (3, 5):
        K = GF(m)
        q = K.q
        ds = [('d0', d0_table(K))]
        for rho in ([7] if m == 3 else [7, 11]):
            ds.append(('d_rho%d' % rho, d_rho(K, rho)))
        for dn, d in ds:
            hs = [('h0', np.zeros(q, dtype=np.int64)),
                  ('ha3', np.array([K.pw(a, 3) for a in range(q)], dtype=np.int64)),
                  ('hrand', np.array([random.randrange(q) for _ in range(q)], dtype=np.int64))]
            for hn, h in hs:
                r = run_case(K, d, h, 'm%d_%s_%s' % (m, dn, hn))
                print(r['label'], r['walsh_formula_ok'], r['gram_exact_ok'], r['witness_equals_target'],
                      '%.3e' % r['phys_minus_target'], flush=True)
                res.append(r)
    allok = all(r['walsh_formula_ok'] and r['gram_exact_ok'] and r['witness_equals_target']
                and abs(r['phys_minus_target']) < 1e-12 for r in res)
    json.dump({'cases': res, 'all_ok': allok}, open(out, 'w'), indent=1)
    print('P802_ALL_OK' if allok else 'P802_FAIL')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main(sys.argv[1])
