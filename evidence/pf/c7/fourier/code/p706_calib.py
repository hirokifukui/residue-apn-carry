"""P7-06 calibration (C7 lane fourier).  usage: python3 -I -B p706_calib.py M NEXTRA OUT.json
Author-side integer DDT (a1c5_lib.ddt, the C6/a1 arithmetic; cross-checked against c1/code/ddt.ddt on the
first table) -> integer Walsh on the hi digit (v rows, t cols) of every (u,s) block, compared with the
formula of NEW_DERIVATIONS section B (fr_lib.Formula) for ALL u in G = F minus {0,rho}, all s, all (eta,xi).
Normalisation: hat = H C_block H (integers, C = DDT counts); claim hat = q * rhs; That = hat/(q N) = rhs/q^2.
Also (for the R1 coupling map): Z (u=0) and E (u=rho) block formulas, and block norms on R and on W
(W = R minus {0}, C6 a1c6_word definition of tau), dense float64 SVD (m <= 5).
"""
import sys, os, json, time, importlib.util
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fr_lib as FL

m = int(sys.argv[1]); nextra = int(sys.argv[2]); outp = sys.argv[3]
K, tabs = FL.tables(m, nextra); q = K.q; N = q * q
add, neg, sub, J = FL.ring_ops(m)
par = FL.parity_table(q)

# c1 author DDT (independent code path) for a cross-check of the DDT itself
c1dir = os.path.join(FL.P, 'c1', 'code'); sys.path.insert(0, c1dir)
spec = importlib.util.spec_from_file_location('c1ddt', os.path.join(c1dir, 'ddt.py'))
c1ddt = importlib.util.module_from_spec(spec); spec.loader.exec_module(c1ddt)

sv = lambda Z: float(np.linalg.norm(Z, 2)) if Z.size else 0.0
out = {'m': m, 'q': q, 'normalisation': 'hat = H*C_block*H (integer DDT counts); claim hat == q*rhs; orthonormal prob. entry That = rhs/q^2; |rhs|<=4 <=> |That|<=4/q^2',
       'bounds_candidate': {'G2': 4 * (1.5 ** m - 1) / q, 'Z2_W': 2 * (3 ** m - 2 * q + 1) / q ** 2, 'E2': 3 / q},
       'tables': {}}
first = True
for name, F in tabs.items():
    t0 = time.time()
    info = FL.extract_pd(K, F); rho = int(info['rho']); p, h, d = info['p'], info['h'], info['d']
    B = J(F); C = FL.ddt(m, B)
    rec = {'rho': rho, 'wt_rho': int(bin(rho).count('1'))}
    if first:
        C1 = c1ddt.ddt(m, B); rec['c1_ddt_equal'] = bool(np.array_equal(C, C1)); assert rec['c1_ddt_equal']; first = False
    fo = FL.Formula(K, info)
    st = dict(n_coeff_compared=0, n_G_entries_nonzero_masks=0, max_abs_rhs_nonzero=0, max_fiber_nonzero=0,
              fiber_values_nonzero=set(), absrhs_hist={}, coset_fibres_ok=True,
              eta0_szxi_nonzero_entries=0, eta0_szxi_nonzero_all_empty=True,
              eta0_szxi0_entries=0, eta0_szxi0_fiber_is_q=True, eta0_szxi0_max_abs_rhs=0,
              etanz_szxi0_entries=0, etanz_szxi0_all_empty=True)
    Mhat = np.zeros((q * (q - 1), q * (q - 1)))            # rows (u,eta!=0), cols (s,xi!=0) on R
    a = np.arange(q); xi = np.arange(q)
    for u in range(q):
        for s in range(q):
            blk = C[u + q * a[:, None], s + q * a[None, :]]
            hat = FL.fwht2(blk)
            Mhat[u * (q - 1):(u + 1) * (q - 1), s * (q - 1):(s + 1) * (q - 1)] = hat[1:, 1:] / (q * N)
            szx = (s & xi)                                   # s*xi per column
            if u in fo.G:
                R, Fb = fo.rhs(u, s)
                assert np.array_equal(hat, q * R), (name, u, s)
                st['n_coeff_compared'] += q * q
                nz = np.ix_(np.arange(1, q), np.arange(1, q))
                st['n_G_entries_nonzero_masks'] += (q - 1) ** 2
                st['max_abs_rhs_nonzero'] = max(st['max_abs_rhs_nonzero'], int(np.abs(R[nz]).max()))
                st['max_fiber_nonzero'] = max(st['max_fiber_nonzero'], int(Fb[nz].max()))
                st['fiber_values_nonzero'] |= set(np.unique(Fb[1:, :][:, szx != 0]).tolist())
                for v_, c_ in zip(*np.unique(np.abs(R[nz]), return_counts=True)):
                    st['absrhs_hist'][int(v_)] = st['absrhs_hist'].get(int(v_), 0) + int(c_)
                eta, chi = fo.atoms(u, s)
                if not (np.array_equal(eta, eta[:, a ^ rho]) and np.array_equal(eta, eta[:, a ^ u])):
                    st['coset_fibres_ok'] = False
                c0 = szx != 0
                st['eta0_szxi_nonzero_entries'] += int(c0.sum())
                if Fb[0, c0].any(): st['eta0_szxi_nonzero_all_empty'] = False
                st['eta0_szxi0_entries'] += int((~c0).sum())
                if not np.all(Fb[0, ~c0] == q): st['eta0_szxi0_fiber_is_q'] = False
                st['eta0_szxi0_max_abs_rhs'] = max(st['eta0_szxi0_max_abs_rhs'], int(np.abs(R[0, ~c0]).max()))
                st['etanz_szxi0_entries'] += int((q - 1) * (~c0).sum())
                if Fb[1:, ~c0].any(): st['etanz_szxi0_all_empty'] = False
            elif u == 0:     # Z formula: rhs = [s*xi=0] sum_a (-1)^{<eta, s/d(a)>}
                w = K.MUL[s, K.INV[d]]
                Rz = np.array([[(1 - 2 * par[e & w]).sum() for _ in range(1)] for e in range(q)])[:, 0]
                R = np.where((szx == 0)[None, :], Rz[:, None], 0)
                assert np.array_equal(hat, q * R), ('Z', name, s)
            else:            # E formula (u=rho): rhs = [s*xi=0] sum_a (-1)^{<eta,v_a> + <xi,D_rho p(a)>}
                va = K.MUL[s ^ h[a ^ rho] ^ h, K.INV[d]] ^ (a & rho)
                Dr = p[a ^ rho] ^ p
                R = (1 - 2 * (par[a[:, None] & va[None, :]][:, None, :] ^ par[xi[:, None] & Dr[None, :]][None, :, :])).sum(2)
                R = np.where((szx == 0)[None, :], R, 0)
                assert np.array_equal(hat, q * R), ('E', name, s)
    st['fiber_values_nonzero'] = sorted(st['fiber_values_nonzero'])
    rec['P706'] = st
    # ---- coupling: block norms on R (Walsh) and on W (C6 definition) ----
    rowsG = np.concatenate([np.arange(u * (q - 1), (u + 1) * (q - 1)) for u in fo.G])
    rZ = np.arange(0, q - 1); rE = np.arange(rho * (q - 1), (rho + 1) * (q - 1))
    csn0 = np.arange(q - 1, q * (q - 1))
    nR = {'full': sv(Mhat), 'G': sv(Mhat[rowsG]), 'Z': sv(Mhat[rZ]), 'Z_s_ne0': sv(Mhat[np.ix_(rZ, csn0)]), 'E': sv(Mhat[rE]),
          'G_cols_s0_max_abs': float(np.abs(Mhat[np.ix_(rowsG, np.arange(q - 1))]).max())}
    lo = np.arange(1, N) & (q - 1); cnt = np.bincount(lo, minlength=q).astype(float)
    Tw = C[1:, 1:] / N
    Ml = (lo[:, None] == lo[None, :]) / cnt[lo][None, :]; Mp = np.eye(N - 1) - Ml
    Mw = Mp @ Tw.T @ Mp                                     # tau = ||Mw||, columns = input alpha in W
    colsG = np.nonzero(np.isin(lo, fo.G))[0]
    nW = {'tau': sv(Mw), 'G': sv(Mw[:, colsG]), 'Z': sv(Mw[:, lo == 0]), 'E': sv(Mw[:, lo == rho])}
    nW['tau2_le_sum'] = bool(nW['tau'] ** 2 <= nW['G'] ** 2 + nW['Z'] ** 2 + nW['E'] ** 2 + 1e-12)
    nW['G_W_equals_G_R'] = bool(abs(nW['G'] - nR['G']) < 1e-10)
    nW['E_W_le_E_R'] = bool(nW['E'] <= nR['E'] + 1e-12); nW['Z_W_le_Z_R_s_ne0'] = bool(nW['Z'] <= nR['Z_s_ne0'] + 1e-12)
    bc = out['bounds_candidate']
    nW['within_candidate_bounds'] = bool(nR['G'] ** 2 <= bc['G2'] and nW['Z'] ** 2 <= bc['Z2_W'] and nR['E'] ** 2 <= bc['E2'])
    nW['sqrtq_tau'] = float(np.sqrt(q) * nW['tau'])
    rec['norms_R_walsh'] = nR; rec['norms_W'] = nW; rec['sec'] = round(time.time() - t0, 1)
    out['tables'][name] = rec
    print(name, json.dumps(rec), flush=True)
    json.dump(out, open(outp, 'w'), indent=1)
print('P706_CALIB=PASS')
