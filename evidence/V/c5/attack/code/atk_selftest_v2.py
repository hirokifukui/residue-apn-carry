"""ATK self-test v2 (v1 compared G_theta_true with V2-L2; correct target is V2 itself, since S1^{-1}(X3_j;K3_j)=V2_j): (1) matmul kernel == literal definition on random (kappa, j, k, c); (2) == C4 p4lib.Z4Conv (FFT) on
all (k, c) for a few kappa; (3) SplitTail at small m: enc/dec round trip, permutation of R^w (m=3, w=2: all 4096 points);
(4) oracle property P (V2 ring sums 0 on one-word slices).  usage: python3 -I -B atk_selftest.py OUT.json"""
import os, sys, json, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
from atk_common import (natural_table, pd_inverse_table, toy_m2_table, hypotheses, save_table, build_cipher, Public,
                        make_cipher_oracle, mds2, random_unit_matrix, sha_arr, APN, ringlib)
from atk_fullblind import Kernel, make_slices, all_tuples, G_theta
sys.path.insert(0, os.path.join(APN, 'c4', 'attack', 'code'))
from p4lib import Z4Conv, ringsum                         # noqa: E402  (C4, read only)


def tables():
    R = ringlib.GR4(3); e = {1, 3, 9}
    Tn = R.encode(R.horner(e, R.all)).astype(np.int64)
    return {'nat_m3_X+X3+X9': save_table('F_nat_m3_X1_X3_X9', Tn),
            'pd_m3_inv_h0': save_table('F_pd_m3_inv_h0', pd_inverse_table(3, 'h0')),
            'pd_m3_inv_a3': save_table('F_pd_m3_inv_a3', pd_inverse_table(3, 'a3')),
            'toy_m2_affine': save_table('F_toy_m2', toy_m2_table())}


def main(outp):
    t0 = time.time(); out = {'tables': {}}
    tb = tables()
    for name, p in tb.items():
        T = np.load(p); m = 2 if 'm2' in name else 3
        out['tables'][name] = {'path': os.path.relpath(p, APN), 'array_sha256': sha_arr(T), 'hyp': hypotheses(T, m)}
    rng = np.random.default_rng(1)
    for name in ('nat_m3_X+X3+X9', 'pd_m3_inv_h0', 'pd_m3_inv_a3', 'toy_m2_affine'):
        m = 2 if 'm2' in name else 3
        c = build_cipher(m, 2, tb[name], mds2()); pub = Public(c); ker = Kernel(pub); N = pub.N
        rec = {}
        # (3) round trip / permutation on all N^2 inputs, 2 keys
        X = np.arange(N * N); xs = [X // N, X % N]
        for ks in range(2):
            q, rev, _ = make_cipher_oracle(c, 900 + ks); k = rev()
            y = c.enc(xs, k); back = c.dec(y, k)
            rec[f'roundtrip_key{ks}'] = bool(all(np.array_equal(back[j], xs[j]) for j in range(2)))
            rec[f'perm_key{ks}'] = len(set((y[0] * N + y[1]).tolist())) == N * N
            # (4) property P on 3 slices
            sl, _ = make_slices(N, 2, 3, 77)
            rec[f'propP_key{ks}'] = all(int(v) == 0 for qq in sl for v in ringsum(np.stack(c.states(qq, k)['V2']), m))
            # true theta passes literal test
            M3inv = pub.M3inv
            L3 = k['L3']; cvec = [int(v[0]) for v in c.rg.mat_apply(M3inv, [np.array([v]) for v in L3])]
            th = {'K4': [kk[0] for kk in k['K4']], 'c': cvec, 'K3': [kk[0] for kk in k['K3']]}
            Vt = [G_theta(ker, th, c.enc(qq, k)) for qq in sl]
            rec[f'G_true_equals_V2_key{ks}'] = all(
                np.array_equal(Vt[t][j], c.states(sl[t], k)['V2'][j]) for t in range(3) for j in range(2))
        # (1) kernel vs literal
        bad = 0; tests = 0
        for _ in range(40):
            Y = [rng.integers(0, N, N) for _ in range(2)]
            kap = rng.integers(0, N, (3, 2)); V = ker.V3(Y, kap)
            for j in range(2):
                z = ker.z(j, V); acc = ker.accept(z)
                for b in range(3):
                    for _ in range(30):
                        kk, cc = int(rng.integers(N)), int(rng.integers(N))
                        tests += 1; bad += acc[b, kk, cc] != ker.accept_literal(z[b], kk, cc)
                    # force some zeros: check all (k,c) with acc True literally
                    for kk, cc in zip(*np.nonzero(acc[b])):
                        tests += 1; bad += not ker.accept_literal(z[b], int(kk), int(cc))
        rec['kernel_vs_literal'] = {'tests': tests, 'mismatch': int(bad)}
        # (2) kernel vs C4 FFT (all k, c)
        conv = Z4Conv(c.rg, c.sb, np.arange(N)); mism = 0; cells = 0
        for _ in range(8):
            Y = [rng.integers(0, N, N) for _ in range(2)]
            kap = rng.integers(0, N, (1, 2)); V = ker.V3(Y, kap)
            for j in range(2):
                z = ker.z(j, V); a1 = ker.accept(z)[0]; a2 = conv.zero_mask(z[0])
                mism += int((a1 != a2).sum()); cells += a1.size
        rec['kernel_vs_C4_FFT'] = {'cells': cells, 'mismatch': mism}
        out[name] = rec; print(name, rec, flush=True)
    out['seconds'] = round(time.time() - t0, 1)
    ok = all(v is True or (isinstance(v, dict) and v.get('mismatch', 0) == 0)
             for name in out if name not in ('tables', 'seconds') for v in out[name].values())
    out['SELFTEST'] = 'PASS' if ok else 'FAIL'
    json.dump(out, open(outp, 'w'), indent=1, default=str); print('SELFTEST=' + out['SELFTEST'], out['seconds'])
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
