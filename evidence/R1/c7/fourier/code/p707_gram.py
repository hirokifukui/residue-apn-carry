"""P7-07 Gram of the G block, small-dimension exact counting (C7 lane fourier).
usage: python3 -I -B p707_gram.py M NEXTRA OUT.json [TABLES comma-separated or 'all']
g = q^2 * G (integer 'count units'): rows r=(u,eta), u in G=F minus {0,rho}, eta != 0; cols c=(s,xi), xi != 0, all s.
g[r,c] = sum over the fibre {a : eta = M*_{A_a}(s AND xi)} of chi = (-1)^{<xi,D_up(a)>+<s AND xi,C_a>}  (fr_lib.Formula;
the formula is checked against the author DDT in p706_calib for m=3,5).  GG* = g g^T / q^4.
Split of Q := g g^T (integers):
  D  = diag(Q)                         (i)   [atom split: I (a'=a), P_rho (a'=a+rho), P_u (a' in a+u+{0,rho})]
  S  = blockdiag_u(g_u g_u^T) - D      (ii)  same u, different eta (different V_u-cosets)
  X  = Q - blockdiag_u(g_u g_u^T)      (iii) different u (cross terms)
h-uniform majorant (derived in notes/P7-07_fourier.md): |Q[r,r']| <= Maj[r,r'] := sum over atom pairs (u,a),(u',a') with
  z_a(eta) = z_a'(eta') of 3^(m - wt(z OR delta)),  delta = D_up(a) + D_u'p(a').
  Row sums of Maj <= U_m := 4 q^2 (3^m - q)  (needs only: fibres = cosets of <rho,u>, p a permutation).
m <= 5: Q in float64 (exact integers), dense eigvalsh, full Maj matrix (entrywise check).
m = 7 : g, Q in float32 (exact: every partial sum < 2^24), Lanczos (scipy eigsh) for norms of Q and X,
        exact per-u eigvalsh for S, Maj only through exact row sums (histogram method).
Norms from eigvalsh / eigsh are numerical (calibration), NOT certificates.  Frobenius norms and row sums are exact integers.
"""
import sys, os, json, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fr_lib as FL

m = int(sys.argv[1]); nextra = int(sys.argv[2]); outp = sys.argv[3]
sel = sys.argv[4] if len(sys.argv) > 4 else 'all'
K, tabs = FL.tables(m, nextra); q = K.q
if sel != 'all':
    tabs = {k: tabs[k] for k in sel.split(',')}
big = m >= 7
dt = np.float32 if big else np.float64
wt = FL.wt_table(q)
X_ = np.arange(q)
T3 = 3 ** (m - wt[X_[:, None] | X_[None, :]])          # T3[z,w] = 3^(m - wt(z|w))
XOR = X_[:, None] ^ X_[None, :]
U_m = 4 * q * q * (3 ** m - q)

out = {'m': m, 'q': q, 'units': 'Q = g g^T, g = q^2*G (integers); GG* = Q/q^4; norms below given both as Q-values and as GG*-values',
       'U_m_rowsum_bound_Q': U_m, 'U_m_rowsum_bound_GGstar': U_m / q ** 4, 'tables': {}}


def eig_max_abs(Mx):
    w = np.linalg.eigvalsh(Mx.astype(np.float64)); return float(max(abs(w[0]), abs(w[-1])))


for name, F in tabs.items():
    t0 = time.time()
    info = FL.extract_pd(K, F); fo = FL.Formula(K, info); rho = fo.rho; Gs = fo.G; nG = len(Gs)
    nr, nc = nG * (q - 1), q * (q - 1)
    g = np.zeros((nr, nc), dtype=dt)
    Iat = np.zeros(nr, np.int64); Prho = np.zeros(nr, np.int64); Pu = np.zeros(nr, np.int64)
    a = np.arange(q); xi = np.arange(q)
    Acoef, Dpu = {}, {}
    for iu, u in enumerate(Gs):
        A, _, Dp = fo.coeffs(u, 0); Acoef[u] = A; Dpu[u] = Dp
        for s in range(q):
            eta, chi = fo.atoms(u, s)
            idx = (eta * q + xi[:, None]).ravel()
            R = np.bincount(idx, weights=chi.ravel(), minlength=q * q).reshape(q, q)
            g[iu * (q - 1):(iu + 1) * (q - 1), s * (q - 1):(s + 1) * (q - 1)] = R[1:, 1:]
            ok = (eta > 0) & (xi[:, None] > 0)
            rows = iu * (q - 1) + eta[ok] - 1
            Iat += np.bincount(rows, minlength=nr)
            Prho += np.bincount(rows, weights=(chi * chi[:, a ^ rho])[ok], minlength=nr).astype(np.int64)
            Pu += np.bincount(rows, weights=(chi * (chi[:, a ^ u] + chi[:, a ^ u ^ rho]))[ok], minlength=nr).astype(np.int64)
    rec = {'rho': int(rho), 'shape_G': [nr, nc]}
    # ---- h-independent support counts ----
    supp = (np.abs(g) > 0) if False else None
    ncols = Iat // 4                                     # fibres have exactly 4 atoms (coset of <rho,u>)
    rec['support'] = {'row_ncols_max': int(ncols.max()), 'row_ncols_min': int(ncols.min()), 'row_ncols_mean': float(ncols.mean()),
                      'col_atoms_per_u': q, 'note': 'support pattern of G depends only on d (A_a), not on p,h'}
    Hall = np.zeros(q, np.int64)
    for u in Gs: Hall += np.bincount(Dpu[u], minlength=q)
    coh = [int((Hall - np.bincount(Dpu[u], minlength=q))[Dpu[u]].max()) for u in Gs]
    rec['coherent_cross_pairs_max_per_atom'] = max(coh)   # #{(u'!=u,a'): D_u'p(a') = D_up(a)} <= q
    rec['Hall_max'] = int(Hall.max()); rec['Hall_0'] = int(Hall[0])
    # ---- Gram ----
    Q = g @ g.T                                           # exact integers
    D = np.diag(Q).astype(np.int64)
    assert np.array_equal(D, Iat + Prho + Pu), 'diag split'
    BD = np.zeros_like(Q)
    for iu in range(nG):
        sl = slice(iu * (q - 1), (iu + 1) * (q - 1)); BD[sl, sl] = Q[sl, sl]
    Sm = BD.copy(); Sm[np.diag_indices(nr)] = 0
    Xm = Q - BD
    def fro2(Mx):
        tot = 0
        for i in range(0, Mx.shape[0], 2048):
            blk = np.rint(Mx[i:i + 2048].astype(np.float64)).astype(np.int64); tot += int((blk * blk).sum())
        return tot
    def rowsum_max(Mx):
        return int(max(np.rint(np.abs(Mx[i:i + 2048].astype(np.float64)).sum(1)).max() for i in range(0, Mx.shape[0], 2048)))
    nrm = {}
    nrm['fro2_Q'] = fro2(Q); nrm['fro2_D'] = int((D * D).sum()); nrm['fro2_S'] = fro2(Sm); nrm['fro2_X'] = fro2(Xm)
    nrm['fro2_I'] = int((Iat * Iat).sum()); nrm['fro2_Prho'] = int((Prho * Prho).sum()); nrm['fro2_Pu'] = int((Pu * Pu).sum())
    nrm['fro2_g'] = int(D.sum())
    nrm['op_D'] = int(np.abs(D).max()); nrm['op_I'] = int(Iat.max()); nrm['op_Prho'] = int(np.abs(Prho).max()); nrm['op_Pu'] = int(np.abs(Pu).max())
    nrm['op_S'] = max(eig_max_abs(Sm[iu * (q - 1):(iu + 1) * (q - 1), iu * (q - 1):(iu + 1) * (q - 1)]) for iu in range(nG))
    if not big:
        nrm['op_Q'] = eig_max_abs(Q); nrm['op_X'] = eig_max_abs(Xm); nrm['op_DS'] = eig_max_abs(BD)
        wS = np.linalg.eigvalsh(Sm.astype(np.float64)); nrm['S_numrank'] = int((np.abs(wS) > 1e-9 * np.abs(wS).max()).sum())
    else:
        from scipy.sparse.linalg import eigsh, LinearOperator
        def lam(Mx):
            op = LinearOperator(Mx.shape, matvec=lambda v: (Mx @ v.astype(np.float32)).astype(np.float64), dtype=np.float64)
            w = eigsh(op, k=1, which='LM', tol=1e-8, maxiter=5000, return_eigenvectors=False); return float(abs(w[0]))
        nrm['op_Q'] = lam(Q); nrm['op_X'] = lam(Xm); nrm['op_DS'] = lam(BD); nrm['op_method'] = 'eigsh Lanczos (numerical)'
    nrm['rowsum_abs_Q_max'] = rowsum_max(Q); nrm['rowsum_abs_X_max'] = rowsum_max(Xm); nrm['rowsum_abs_S_max'] = rowsum_max(Sm)
    rec['Q_int'] = nrm
    s4 = float(q) ** 4
    rec['GGstar'] = {k.replace('fro2', 'fro'): (float(np.sqrt(v)) / s4 if k.startswith('fro2') else v / s4)
                     for k, v in nrm.items() if isinstance(v, (int, float)) and not k.endswith('numrank')}
    rec['GGstar']['normG'] = float(np.sqrt(nrm['op_Q'])) / q ** 2
    rec['GGstar']['sqrtq_normG'] = float(np.sqrt(q)) * rec['GGstar']['normG']
    rec['GGstar']['q_opQ'] = q * nrm['op_Q'] / s4
    del Q, BD, Sm
    # ---- majorant row sums (histogram method, exact integers) ----
    FX_all = np.stack([T3[z][XOR] @ Hall for z in range(q)])          # FX_all[z,x] = sum_y Hall[y] T3[z,x^y]
    rs_tot = np.zeros(nr, np.int64); rs_diag = np.zeros(nr, np.int64); rs_S = np.zeros(nr, np.int64); rs_X = np.zeros(nr, np.int64)
    eta_r = np.arange(1, q)
    for iu, u in enumerate(Gs):
        Hu = np.bincount(Dpu[u], minlength=q)
        Fu = np.stack([T3[z][XOR] @ Hu for z in range(q)])
        z = fo.iadj[Acoef[u][None, :], eta_r[:, None]]                  # z[eta-1, a]
        x = Dpu[u][None, :]
        dg = 2 * T3[z, 0] + 2 * T3[z, x ^ Dpu[u][a ^ rho][None, :]]
        sl = slice(iu * (q - 1), (iu + 1) * (q - 1))
        rs_diag[sl] = dg.sum(1); rs_S[sl] = (Fu[z, x] - dg).sum(1); rs_X[sl] = (FX_all[z, x] - Fu[z, x]).sum(1)
        rs_tot[sl] = FX_all[z, x].sum(1)
        assert np.all(z > 0)
    rec['majorant_rowsum'] = {'tot_max': int(rs_tot.max()), 'diag_max': int(rs_diag.max()), 'S_max': int(rs_S.max()), 'X_max': int(rs_X.max()),
                              'tot_max_over_U_m': float(rs_tot.max() / U_m), 'tot_max_GGstar': float(rs_tot.max() / s4),
                              'X_max_GGstar': float(rs_X.max() / s4), 'tot_mean_GGstar': float(rs_tot.mean() / s4)}
    # ---- full majorant matrix + entrywise check (m <= 5) ----
    if not big:
        Q = g @ g.T
        Maj = np.zeros((nr, nr), np.int64)
        for iu, u in enumerate(Gs):
            z = fo.iadj[Acoef[u][None, :], eta_r[:, None]]              # (q-1, q)
            r_idx = iu * (q - 1) + eta_r - 1
            for ju, u2 in enumerate(Gs):
                eta2 = fo.adj[Acoef[u2][None, None, :], z[:, :, None]]    # (q-1, q, q) : [eta, a, a']
                dl = Dpu[u][None, :, None] ^ Dpu[u2][None, None, :]
                w = T3[z[:, :, None], dl]
                rr = np.broadcast_to(r_idx[:, None, None], w.shape); cc = ju * (q - 1) + eta2 - 1
                np.add.at(Maj, (rr.ravel(), cc.ravel()), w.ravel())
        assert np.array_equal(Maj, Maj.T)
        rec['majorant_matrix'] = {'entrywise_absQ_le_Maj': bool(np.all(np.abs(np.rint(Q)).astype(np.int64) <= Maj)),
                                  'rowsum_equals_hist_method': bool(np.array_equal(Maj.sum(1), rs_tot)),
                                  'op_Maj_GGstar': eig_max_abs(Maj.astype(np.float64)) / s4}
        del Q, Maj
    rec['sec'] = round(time.time() - t0, 1)
    out['tables'][name] = rec
    print(name, json.dumps(rec), flush=True)
    json.dump(out, open(outp, 'w'), indent=1)
    del g, Xm
print('P707_GRAM=PASS')
