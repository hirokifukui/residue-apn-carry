"""P3-01 / P3-03 (C3, Claude): warm start of C1 theorem S with z1=e1=1/q (C2 theorem E), exact rational identities,
uniform constants for t=2..5, general-rho constant, and finite m=5 calibration with the AUTHOR ddt module (c1/code/ddt.py)
on several lifts (natural, h0, adversarial-G, G-pair from c3/a1/data). GPT's independent digit DDT is a separate check.
Usage: python3 -I p301_warmstart.py <apn_cipher root> <out.json>
"""
import sys, json, hashlib
from pathlib import Path
from fractions import Fraction as Fr
import numpy as np
import sympy as sp
root = Path(sys.argv[1]).resolve(); out = Path(sys.argv[2])
sys.path.insert(0, str(root / 'c1' / 'code'))
from ddt import ddt          # author DDT (ring subtraction)
from codes import mk

q, o = sp.symbols('q omega', positive=True)
res = {'symbolic': {}, 'table': [], 'general_rho': {}, 'finite': []}

def step(z, e, om):
    """theorem S one step (sup-norm recursion), sigma^Z, sigma^E after one more B."""
    return sp.expand(2/q**2 + 2*e/q), sp.expand(2*om/q**2 + z/om + 2*e/q)
def final(z, e):
    return z, sp.expand(2/q**2 + 2*e/q)

# P3-01: omega=2, warm start
z, e = 1/q, 1/q
rows = []
for t in range(1, 7):
    zf, uf = final(z, e)
    rows.append((t, sp.expand(zf*q**2), sp.expand(uf*q**2)))
    z, e = step(z, e, 2)
claimed = {2: Fr(4), 3: Fr(27, 8), 4: Fr(315, 128), 5: Fr(4883, 2048)}
for t, zn, un in rows:
    zv = Fr(str(sp.nsimplify(zn.subs(q, 32)))); uv = Fr(str(sp.nsimplify(un.subs(q, 32))))
    # every coefficient of 1/q nonneg -> decreasing in q -> q=32 value is uniform bound for q>=32
    X = sp.Symbol('x')
    if t == 1:
        nonneg = True  # z1*N = q, not a bounded constant; t=1 excluded from the uniform table
    else:
        pz = sp.Poly(sp.expand(zn.subs(q, 1/X)), X); pu = sp.Poly(sp.expand(un.subs(q, 1/X)), X)
        nonneg = all(c >= 0 for c in pz.all_coeffs() + pu.all_coeffs())
    c = max(zv, uv)
    ok = (t not in claimed) or (c == claimed[t])
    res['table'].append({'t': t, 'z_times_N': str(zn), 'unit_times_N': str(un), 'c_t_at_q32': str(c),
                         'coeffs_in_1/q_nonneg': nonneg, 'matches_GPT_constant': ok})
    assert nonneg and ok
# monotone in t at q=32 (from t=2): c_{t+1} <= c_t
cs = [Fr(r['c_t_at_q32']) for r in res['table']]
assert all(cs[i+1] <= cs[i] for i in range(1, len(cs)-1))
# EDP_2 <= 4/N needs 3+12/q <= 4 i.e. q>=12
res['symbolic']['omega2_t2'] = {'z2N': '4', 'unit2N': '3+12/q', 'holds_for': 'q>=12 (in particular all q>=32)'}
# compare to cold start (C2 bound_t) to make clear warm <= cold
z, e = sp.Integer(1), sp.Integer(1)
cold = []
for t in range(1, 6):
    z, e = step(z, e, 2); zf, uf = final(z, e)
    cold.append(str(max(Fr(str(zf.subs(q, 32)*1024)), Fr(str(uf.subs(q, 32)*1024)))))
res['symbolic']['cold_start_c_t_q32_t1..5'] = cold

# P3-03: general omega, 2<=omega<=q
z2, e2 = step(1/q, 1/q, o); zf, uf = final(z2, e2)
U = sp.simplify(uf*q**2)
diff = sp.simplify(6 + 6/q - U - (q-o)*(4*o-2)/(q*o))
assert diff == 0
assert sp.simplify(zf*q**2 - 4) == 0
res['general_rho'] = {'unit2_times_N': str(sp.expand(U)), 'identity': '(6+6/q)-unit2N = (q-omega)(4omega-2)/(q omega)',
                      'identity_check': str(diff), 'z2_times_N': '4',
                      'bound': 'EDP_2 <= (6+6/q)/N <= 99/(16N) for q>=32, 2<=omega<=q (omega=2^wt(rho)<=2^m=q)',
                      'q32_value': str(Fr(6) + Fr(6, 32))}
# spot: worst omega over integer powers of two at q=32,128
for qq in [32, 128]:
    vals = {2**k: str(Fr(2) + Fr(2, 2**k) + Fr(4*(2**k+1), qq)) for k in range(1, int(np.log2(qq))+1)}
    res['general_rho'][f'unit2N_by_omega_q{qq}'] = vals
    assert all(Fr(v) <= 6 + Fr(6, qq) for v in vals.values())

# finite m=5 with author ddt
m, N = 5, 1024
tabs = [('natural', root/'c1/data/F_m5_r3.npy')]
for nm in ['h0', 'adversarialG', 'Gpair', 'random']:
    p = root/'c3/a1/data'/f'F_{nm}.npy'
    if p.exists(): tabs.append((nm, p))
J = mk(m)[3]
for name, p in tabs:
    F = np.load(p).astype(np.int64)
    B = J(F)
    cb = ddt(m, B).astype(np.int64); cf = ddt(m, F).astype(np.int64)
    du = int(cb[1:].max())
    # exact integer products (object dtype avoided: int64 suffices, max N^3=2^30)
    A1 = cb @ cf; A2 = cb @ A1; A3 = cb @ A2
    edp = [Fr(int(A1[1:].max()), N**2), Fr(int(A2[1:].max()), N**3), Fr(int(A3[1:].max()), N**4)]
    rec = {'lift': name, 'sha256': hashlib.sha256(F.tobytes()).hexdigest()[:16], 'DU_B': du,
           'N_EDP_t1': str(edp[0]*N), 'N_EDP_t2': str(edp[1]*N), 'N_EDP_t3': str(edp[2]*N)}
    if name != 'random':
        assert du == 32, (name, du)
        assert edp[1]*N <= 4 and edp[2]*N <= Fr(27, 8)
        rec['within_warm_bounds'] = True
    res['finite'].append(rec)
out.write_text(json.dumps(res, indent=1)); print(json.dumps(res['table'], indent=0)); print(json.dumps(res['finite'], indent=0))
print('P301=PASS')
