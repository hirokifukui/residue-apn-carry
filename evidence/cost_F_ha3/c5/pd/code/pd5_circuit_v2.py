#!/usr/bin/env python3
"""P5-09 v2 (C5, Claude PD lane; v1 pd5_circuit.py aborted at m7 on a zero row of the d0 linear map -> v2 adds a
cost-free CONST0 node for all-zero rows, counted 0 gates as in C4 p413 lin_xor): explicit gate DAG for the PD S-box F(a,b) = (x^{-1}(a), h(a) xor d0(a) b), h in {0, a^3},
with h = a^3 taken from the EXISTING Itoh-Tsujii node b2 = a^2 * a (no new multiplication).
Bit model = C4 COST_P4 rule (c4/cost/p413_cost.py): F_{2^m} product = schoolbook (m^2 AND, partial-product XORs
(m^2 - (2m-1)) + naive reduction XORs); F2-linear maps (squarings, d0 linear part) = naive row XOR (row weight - 1);
the constant 1 of d0 = one NOT on bit 0.  This is ONE circuit (upper bound), not a minimal circuit.
The DAG is built gate by gate (node list), evaluated bit-sliced on ALL 2^(2m) inputs and compared to reference tables:
  m5: c5/pd/data/F_PD_h0_m5.npy, F_PD_hX3_m5.npy (this lane), c4/pd/data/F_pd_inv_m5.npy (C4 h0),
      gpt_input/.../auditor_PD_inverse_hX3_m5.npy (auditor)
  m7: c5/pd/data/F_PD_h0_m7.npy, F_PD_hX3_m7.npy (pd5_m7.py)
Chains (C4 p413 inverse_chain):  m5: b2 = b1^2 b1, b4 = b2^(2^2) b2, inv = b4^2
                                 m7: b2 = b1^2 b1, b3 = b2^2 x, b6 = b3^(2^3) b3, inv = b6^2
usage: python3 -I -B pd5_circuit.py OUT.json
"""
import os, sys, json, time, hashlib
sys.dont_write_bytecode = True
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pd5_math import gf_mul_table, gf_pow, APN, DATA, sha_arr, sha_file   # noqa: E402

MODS = {5: 0b100101, 7: 0b10000011}


class DAG:
    def __init__(self):
        self.nodes = []          # (op, args, label)

    def add(self, op, args=(), label=''):
        self.nodes.append((op, tuple(args), label)); return len(self.nodes) - 1

    def inp(self, label): return self.add('IN', (), label)
    def AND(self, x, y): return self.add('AND', (x, y))
    def XOR(self, x, y): return self.add('XOR', (x, y))
    def NOT(self, x): return self.add('NOT', (x,))

    def counts(self):
        c = {'AND': 0, 'XOR': 0, 'NOT': 0, 'IN': 0, 'CONST0': 0}
        for op, _, _ in self.nodes: c[op] += 1
        return c

    def evaluate(self, inputs):
        val = []
        for op, args, label in self.nodes:
            if op == 'IN': val.append(inputs[label])
            elif op == 'CONST0': val.append(np.zeros_like(inputs['a0']))
            elif op == 'AND': val.append(val[args[0]] & val[args[1]])
            elif op == 'XOR': val.append(val[args[0]] ^ val[args[1]])
            else: val.append(~val[args[0]])
        return val

    def fanout(self):
        f = [0] * len(self.nodes)
        for op, args, _ in self.nodes:
            for a in args: f[a] += 1
        return f


def xor_chain(g, terms):
    acc = terms[0]
    for t in terms[1:]: acc = g.XOR(acc, t)
    return acc


def linmap(g, xs, fun, m):
    """F2-linear map given by python function on field ints; naive row XOR."""
    cols = [fun(1 << j) for j in range(m)]
    out = []
    for i in range(m):
        terms = [xs[j] for j in range(m) if (cols[j] >> i) & 1]
        out.append(xor_chain(g, terms) if terms else g.add('CONST0', (), 'zero_row'))
    return out


def fmul(g, xs, ys, m, mod):
    pp = {}
    for i in range(m):
        for j in range(m): pp.setdefault(i + j, []).append(g.AND(xs[i], ys[j]))
    c = [xor_chain(g, pp[k]) for k in range(2 * m - 1)]
    red = {}
    for k in range(m, 2 * m - 1):
        r = 1 << k
        for kk in range(2 * m - 2, m - 1, -1):
            if (r >> kk) & 1: r ^= mod << (kk - m)
        red[k] = r
    out = []
    for i in range(m):
        out.append(xor_chain(g, [c[i]] + [c[k] for k in range(m, 2 * m - 1) if (red[k] >> i) & 1]))
    return out


def build(m, with_h):
    mod = MODS[m]; MUL = gf_mul_table(m, mod)
    sq = lambda v, k: v if k == 0 else sq(int(MUL[v, v]), k - 1)
    g = DAG(); A = [g.inp(f'a{i}') for i in range(m)]; Bv = [g.inp(f'b{i}') for i in range(m)]
    marks = {}
    s1 = linmap(g, A, lambda v: sq(v, 1), m)
    b2 = fmul(g, s1, A, m, mod); marks['b2=a^3'] = b2
    if m == 5:
        u = linmap(g, b2, lambda v: sq(v, 2), m); b4 = fmul(g, u, b2, m, mod)
        inv = linmap(g, b4, lambda v: sq(v, 1), m); chain = 'b2=b1^2 b1, b4=b2^(2^2) b2, inv=b4^2'
    else:
        u = linmap(g, b2, lambda v: sq(v, 1), m); b3 = fmul(g, u, A, m, mod)
        w = linmap(g, b3, lambda v: sq(v, 3), m); b6 = fmul(g, w, b3, m, mod)
        inv = linmap(g, b6, lambda v: sq(v, 1), m); chain = 'b2=b1^2 b1, b3=b2^2 x, b6=b3^(2^3) b3, inv=b6^2'
    n_chain = g.counts()
    dl = linmap(g, A, lambda v: sq(v, 2) ^ sq(v, 1), m)
    d = [g.NOT(dl[0])] + dl[1:]
    y = fmul(g, d, Bv, m, mod)
    hi = [g.XOR(y[i], b2[i]) for i in range(m)] if with_h else y
    return g, A, Bv, inv, hi, b2, chain, n_chain


def eval_table(g, inv, hi, m):
    N = 1 << (2 * m); X = np.arange(N, dtype=np.int64)
    inputs = {f'a{i}': ((X >> i) & 1).astype(bool) for i in range(m)}
    inputs.update({f'b{i}': ((X >> (m + i)) & 1).astype(bool) for i in range(m)})
    val = g.evaluate(inputs); out = np.zeros(N, np.int64)
    for i in range(m):
        out |= val[inv[i]].astype(np.int64) << i; out |= val[hi[i]].astype(np.int64) << (m + i)
    return out


def main(outp):
    t0 = time.time(); res = {'id': 'P5-09 gate DAG v2', 'rule': 'C4 COST_P4 bit model (schoolbook product, naive linear rows, NOT for d0 constant)'}
    aud = os.path.join(APN, 'gpt_input', 'extracted_P5', 'ResidueAPN_P4_C4_Reviewed_P5_20261011', 'evidence', 'auditor_PD_inverse_hX3_m5.npy')
    refs = {(5, False): [os.path.join(DATA, 'F_PD_h0_m5.npy'), os.path.join(APN, 'c4', 'pd', 'data', 'F_pd_inv_m5.npy')],
            (5, True): [os.path.join(DATA, 'F_PD_hX3_m5.npy'), aud],
            (7, False): [os.path.join(DATA, 'F_PD_h0_m7.npy')],
            (7, True): [os.path.join(DATA, 'F_PD_hX3_m7.npy')]}
    for m in (5, 7):
        for wh in (False, True):
            g, A, Bv, inv, hi, b2, chain, nch = build(m, wh)
            T = eval_table(g, inv, hi, m)
            fo = g.fanout()
            rec = {'m': m, 'h': 'a^3 (=b2 reused)' if wh else '0', 'chain': chain, 'counts': g.counts(),
                   'chain_only_counts': nch, 'nodes': len(g.nodes),
                   'b2_nodes': b2, 'b2_fanout': [fo[i] for i in b2],
                   'eval_table_sha256': sha_arr(T),
                   'match': {os.path.relpath(p, APN): bool(np.array_equal(T, np.load(p).astype(np.int64))) for p in refs[(m, wh)]},
                   'points': 1 << (2 * m)}
            # dump the DAG itself
            dp = os.path.join(APN, 'c5', 'pd', 'results', f'dag_m{m}_{"hX3" if wh else "h0"}_v2.json')
            json.dump({'nodes': [[i, op, list(a), lb] for i, (op, a, lb) in enumerate(g.nodes)],
                       'outputs_lo': inv, 'outputs_hi': hi, 'b2': b2}, open(dp, 'w'))
            rec['dag_file'] = os.path.relpath(dp, APN); rec['dag_file_sha256'] = sha_file(dp)
            res[f'm{m}_{"hX3" if wh else "h0"}'] = rec
            print(m, wh, rec['counts'], rec['match'], rec['b2_fanout'], flush=True)
        c0, c1 = res[f'm{m}_h0']['counts'], res[f'm{m}_hX3']['counts']
        res[f'm{m}_delta_hX3_minus_h0'] = {k: c1[k] - c0[k] for k in ('AND', 'XOR', 'NOT')}
    res['time_s'] = round(time.time() - t0, 1)
    json.dump(res, open(outp, 'w'), indent=1)
    print('DELTA m5', res['m5_delta_hX3_minus_h0'], 'm7', res['m7_delta_hX3_minus_h0'], 'DONE', res['time_s'])


if __name__ == '__main__':
    main(sys.argv[1])
