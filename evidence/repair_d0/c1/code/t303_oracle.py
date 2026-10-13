"""T3-03: independent oracle for GR(4,m), natural lift of P_{m,r}, J, Taylor decomposition.
usage: python3 -I t303_oracle.py OUTDIR      (exit 0 only if every assertion holds)"""
import sys, json, hashlib, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ringlib import GR4, GF2m, P_exponents

def sha(a): return hashlib.sha256(np.ascontiguousarray(a, dtype=np.int64).tobytes()).hexdigest()

def run(m, r, out):
    R = GR4(m); K = GF2m(m); q, N = R.q, R.N
    X = R.all
    exps = P_exponents(m, r)
    Fc = R.horner(exps, X)                         # route 1: Horner over the ring
    F = R.encode(Fc)
    assert len(set(F.tolist())) == N, "F not a permutation"
    # route 2: product form of Prop. C:  P = D*E - 1 - 2(Y+Z), with 0/1 lifts
    def mono(e): return R.horner({e}, X) if e > 0 else np.broadcast_to(R.const(1), X.shape)
    pw = {e: R.horner({e}, X) for e in set([1 << i for i in range(m)])}
    V = sum(pw[1 << i] for i in range(r - 2)) % 4 if r > 2 else 0 * X
    W = pw[1 << (r - 2)]; Y = pw[1 << (m - 2)]; Z = pw[1 << (m - 1)]
    one = R.const(1)
    D = (one + W + Y) % 4; E = (one + V + Y + Z) % 4
    Fc2 = (R.mul(D, E) - one - 2 * (Y + Z)) % 4
    assert np.array_equal(Fc2, Fc), "product form differs"
    # residue / Taylor decomposition, field side computed independently in GF2m
    a_of = X % 2 @ (1 << np.arange(m))             # residue a as m-bit int
    b_of = X // 2 @ (1 << np.arange(m))            # upper digit b as m-bit int
    p = np.zeros(q, dtype=np.int64); h = np.zeros(q, dtype=np.int64)
    sig = R.decode(np.arange(q))                   # sigma(a): 0/1 coefficients = codes 0..q-1
    Fs = R.encode(R.horner(exps, sig))
    p = Fs & (q - 1); h = Fs >> m
    # p from the field directly
    pf = np.array([np.bitwise_xor.reduce([K.pow(a, e) for e in exps]) for a in range(q)])
    assert np.array_equal(p, pf), "residue of lift != P over F_q"
    d = np.array([1 ^ K.pow(a, 1 << (r - 2)) ^ K.pow(a, 1 << (m - 2)) for a in range(q)])
    assert np.all(d != 0)
    vals, cnt = np.unique(d, return_counts=True)
    assert set(cnt.tolist()) == {2} and len(vals) == q // 2
    assert all(d[a] == d[a ^ 1] for a in range(q))          # fibres {a, a+1}: rho = 1
    Kmap = d ^ 1
    ker = [a for a in range(q) if Kmap[a] == 0]
    assert ker == [0, 1]
    # additivity of K
    assert all(Kmap[a ^ c] == Kmap[a] ^ Kmap[c] for a in range(q) for c in range(q))
    pred = p[a_of] | ((h[a_of] ^ K.MUL[d[a_of], b_of]) << m)
    assert np.array_equal(pred, F), "Taylor form F(a,b)=(p(a),h(a)+d(a)b) fails"
    # J
    idx = np.arange(N)
    J = ((idx & (q - 1)) << m) | (idx >> m)
    assert np.array_equal(J[J], idx)
    # J is not additive: witness
    Jc = R.decode(J)
    s1 = R.encode(R.add(Jc[1][None], Jc[1][None]))[0]; s2 = J[R.encode(R.add(X[1][None], X[1][None]))[0]]
    witness = {'x': 1, 'y': 1, 'J(x)+J(y)': int(s1), 'J(x+y)': int(s2)}
    assert s1 != s2
    # unit inverse refuses non-units
    refused = 0
    for z in range(0, N, max(1, N // 64)):
        if not R.is_unit(X[z]):
            try: R.inv_unit(X[z])
            except ValueError: refused += 1
            else: raise AssertionError('non-unit accepted')
    if m == 5:
        for z in range(N):
            if R.is_unit(X[z]):
                assert np.array_equal(R.mul(X[z], R.inv_unit(X[z])), R.const(1))
    res = {'m': m, 'r': r, 'q': q, 'N': N, 'exponents': sorted(exps),
           'F_sha256_int64': sha(F), 'F_first16': F[:16].tolist(),
           'permutation': True, 'product_form_equal': True, 'taylor_form_equal': True,
           'rho': 1, 'd_image_size': int(len(vals)), 'd_fibre_sizes': [2],
           'J_involution': True, 'J_nonadditive_witness': witness,
           'nonunit_inverse_refused_count': refused,
           'p_table': p.tolist(), 'h_table': h.tolist(), 'd_table': d.tolist()}
    np.save(os.path.join(out, f'F_m{m}_r{r}.npy'), F)
    return res

if __name__ == '__main__':
    out = sys.argv[1]; os.makedirs(out, exist_ok=True)
    allres = [run(5, 3, out), run(7, 5, out), run(7, 3, out)]
    with open(os.path.join(out, 't303_oracle.json'), 'w') as fh:
        json.dump(allres, fh, indent=1)
    for x in allres:
        print(x['m'], x['r'], x['F_sha256_int64'], x['F_first16'])
    print('T303=PASS')
