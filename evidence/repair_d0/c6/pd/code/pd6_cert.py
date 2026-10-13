#!/usr/bin/env python3
"""P6-09 step 1 / P6-05 finite check (C6, Claude pd lane, 2026-10-11).  Own GF(2^m) arithmetic (no import of c1..c5 math).
Only tables are READ (c1/c4/c5 data); nothing outside c6/pd is written.

Certificate (NEW_DERIVATIONS A2/A4), for PD tables only (p = x^{q-2}, d = d0 = a^4+a^2+1):
   r = a^2+a+1, H = {Tr = 1}, Delta_h(r) = h(a)+h(a+1),
   A(h) = sum_{r in H} r^-3 Delta_h(r),  B(h) = sum r^-5 Delta_h(r)^2,  ell(h) = A + B^(q/2).
Phi_{kappa,mu}(C) = sum_a (z(a) + d(a) C)^s,  s = q/2-1,  z(a) = h(a) + d(a) (a & kappa) + mu   (coeffs explicit, binom(s,j)=1).
Checks per (table, m): Psi(c) == Phi(c)^2 for all c (all keys for m<=5; sample for m7),
   [C^s]Phi == 0, [C^(s-1)]Phi == A+tau, [C^(s-2)]Phi == B+tau^2 (tau = kappa & 1), Psi-identically-zero key count,
   min over keys of #{c : Psi(c) != 0}, split by tau.
usage: python3 -I -B pd6_cert.py OUT.json
"""
import os, sys, json, time, hashlib
sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
APN = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
MODS = {3: 0b1011, 5: 0b100101, 7: 0b10000011}


def mul_table(m, mod):
    q = 1 << m; x = np.arange(q, dtype=np.int64); T = np.zeros((q, q), np.int64)
    for i in range(m):
        T ^= np.where(((x >> i) & 1)[None, :] == 1, (x << i)[:, None], 0)
    for k in range(2 * m - 2, m - 1, -1):
        T ^= np.where(((T >> k) & 1) == 1, mod << (k - m), 0)
    return T


class GF:
    def __init__(self, m):
        self.m, self.q = m, 1 << m; self.MUL = mul_table(m, MODS[m])
        q = self.q; self.POW = np.zeros((q, q + 1), np.int64); self.POW[:, 0] = 1
        for e in range(1, q + 1): self.POW[:, e] = self.MUL[self.POW[:, e - 1], np.arange(q)]
        a = np.arange(q); self.inv = self.POW[:, q - 2].copy()
        assert all(self.MUL[x, self.inv[x]] == 1 for x in range(1, q))
        tr = np.zeros(q, np.int64); y = a.copy()
        for _ in range(m): tr ^= y; y = self.MUL[y, y]
        assert set(tr.tolist()) <= {0, 1}; self.tr = tr

    def pw(self, x, e):            # x^e, e >= 0 (0^0 = 1)
        return int(self.POW[x, e]) if e <= self.q else int(self.POW[x, e % (self.q - 1) or (self.q - 1)]) if x else 0


def certificate(G, h):
    q, MUL = G.q, G.MUL; a = np.arange(q)
    r = MUL[a, a] ^ a ^ 1; D = h ^ h[a ^ 1]
    Hset = sorted(set(r.tolist())); Ht = sorted(int(x) for x in a if G.tr[x] == 1)
    assert Hset == Ht, 'r(F) != {Tr=1}'
    delta = {}
    for x in range(q):
        rv = int(r[x]); assert delta.get(rv, int(D[x])) == int(D[x]); delta[rv] = int(D[x])
    A = 0; B = 0
    for rv in Hset:
        ri = int(G.inv[rv]); A ^= int(MUL[G.pw(ri, 3), delta[rv]]); B ^= int(MUL[G.pw(ri, 5), MUL[delta[rv], delta[rv]]])
    ell = A ^ G.pw(B, q // 2)
    p1 = 0; p2 = 0; p3 = 0; p5 = 0
    for rv in Hset:
        ri = int(G.inv[rv]); p1 ^= ri; p2 ^= G.pw(ri, 2); p3 ^= G.pw(ri, 3); p5 ^= G.pw(ri, 5)
    return {'A': A, 'B': B, 'ell': ell, 'Omega=A^2+B': int(MUL[A, A]) ^ B, 'ell^2==Omega': G.pw(ell, 2) == (int(MUL[A, A]) ^ B),
            'Delta_distinct_values': len(set(delta.values())), 'H_size': len(Hset),
            'powersums_r^-1,-2,-3,-5': [p1, p2, p3, p5]}


def phi_coeffs(G, h, d, kap, mu):
    q, MUL = G.q, G.MUL; s = q // 2 - 1; a = np.arange(q)
    z = h ^ MUL[d, a & kap] ^ mu
    co = np.zeros(s + 1, np.int64)                       # co[j] = [C^j]Phi = sum_a z^(s-j) d^j
    for j in range(s + 1):
        co[j] = np.bitwise_xor.reduce(MUL[G.POW[z, s - j], G.POW[d, j]])
    return co


def phi_eval(G, co):
    q, MUL = G.q, G.MUL; c = np.arange(q); acc = np.zeros(q, np.int64)
    for j in range(len(co) - 1, -1, -1): acc = MUL[acc, c] ^ co[j]
    return acc


def psi_all(G, p, h, d, kap):
    q, MUL = G.q, G.MUL; a = np.arange(q); c = np.arange(q)[:, None]
    arg = h[None, :] ^ MUL[d[None, :], c ^ (a & kap)[None, :]]
    return np.stack([np.bitwise_xor.reduce(p[arg ^ mu], axis=1) for mu in range(q)])   # [mu, c]


def decompose(F, G):
    q = G.q; a = np.arange(q); p = F[a] & (q - 1); h = F[a] >> G.m; d = (F[a | (1 << G.m)] >> G.m) ^ h
    X = np.arange(q * q); ok = np.array_equal(p[X & (q - 1)] | ((h[X & (q - 1)] ^ G.MUL[d[X & (q - 1)], X >> G.m]) << G.m), F)
    return p, h, d, bool(ok)


def analyse(G, p, h, d, full_phi=True, phi_key_stride=1):
    q, MUL = G.q, G.MUL; s = q // 2 - 1; a = np.arange(q)
    cert = certificate(G, h); A, B = cert['A'], cert['B']
    zero_keys = 0; minnz = {0: q + 1, 1: q + 1}; argmin = {0: None, 1: None}
    psi_eq_phi2 = True; top_ok = True; checked_phi = 0; maxdeg = {0: -1, 1: -1}; mindeg = {0: q, 1: q}
    for kap in range(q):
        P = psi_all(G, p, h, d, kap); tau = kap & 1
        for mu in range(q):
            nz = int(np.count_nonzero(P[mu])); zero_keys += (nz == 0)
            if nz < minnz[tau]: minnz[tau] = nz; argmin[tau] = [kap, mu]
            if full_phi and ((kap * q + mu) % phi_key_stride == 0):
                co = phi_coeffs(G, h, d, kap, mu); checked_phi += 1
                v = phi_eval(G, co); psi_eq_phi2 &= bool(np.array_equal(MUL[v, v], P[mu]))
                top_ok &= (int(co[s]) == 0 and int(co[s - 1]) == (A ^ tau) and int(co[s - 2]) == (B ^ int(MUL[tau, tau])))
                nzc = np.nonzero(co)[0]; dg = int(nzc.max()) if nzc.size else -1
                maxdeg[tau] = max(maxdeg[tau], dg); mindeg[tau] = min(mindeg[tau], dg)
    return {'certificate': cert, 'psi_zero_keys': zero_keys, 'keys': q * q,
            'min_nonzero_c_tau0': minnz[0], 'argmin_tau0': argmin[0], 'min_nonzero_c_tau1': minnz[1], 'argmin_tau1': argmin[1],
            'bound_q/2+2': q // 2 + 2, 'bound_q/2+3': q // 2 + 3,
            'phi_keys_checked': checked_phi, 'psi_eq_phi_sq_all_checked': psi_eq_phi2, 'top3_coeffs_match_A1_all_checked': top_ok,
            'deg_phi_range_tau0': [mindeg[0], maxdeg[0]], 'deg_phi_range_tau1': [mindeg[1], maxdeg[1]]}


def sha_arr(T):
    return hashlib.sha256(np.ascontiguousarray(np.asarray(T).astype(np.int64)).tobytes()).hexdigest()


def main(outp):
    t0 = time.time(); res = {'id': 'P6-09 step1 / P6-05 finite: certificate ell(h) and Phi/Psi on PD tables', 'runs': {}}
    for m in (3, 5, 7):
        G = GF(m); q = G.q; a = np.arange(q)
        inv = G.inv.copy(); d0 = G.POW[:, 4] ^ G.POW[:, 2] ^ 1
        hs = {'h0': np.zeros(q, np.int64), 'hA': a.astype(np.int64), 'hX3': G.POW[:, 3].copy()}
        for nm, h in hs.items():
            stride = 1 if m <= 5 else 61
            r = analyse(G, inv, h, d0, full_phi=True, phi_key_stride=stride)
            r.update({'m': m, 'table': 'own build p=x^-1, d0, h=' + nm, 'field_mod': bin(MODS[m])})
            res['runs'][f'm{m}_{nm}'] = r
            print(f'm{m}', nm, json.dumps({k: r[k] for k in ('psi_zero_keys', 'min_nonzero_c_tau0', 'min_nonzero_c_tau1',
                  'psi_eq_phi_sq_all_checked', 'top3_coeffs_match_A1_all_checked', 'deg_phi_range_tau0', 'deg_phi_range_tau1')}),
                  json.dumps(r['certificate']), round(time.time() - t0, 1), flush=True)
            json.dump(res, open(outp, 'w'), indent=1, default=str)
    # m5 reference tables (read only)
    G = GF(5); q = G.q; d0 = G.POW[:, 4] ^ G.POW[:, 2] ^ 1
    ref = {'natural_F': os.path.join(APN, 'c1', 'data', 'F_m5_r3.npy'),
           'PD_h0': os.path.join(APN, 'c5', 'pd', 'data', 'F_PD_h0_m5.npy'),
           'PD_hC3': os.path.join(APN, 'c4', 'pd', 'data', 'F_pd_inv_hC3_m5.npy'),
           'PD_hX3': os.path.join(APN, 'c5', 'pd', 'data', 'F_PD_hX3_m5.npy')}
    res['m5_tables'] = {}
    for nm, pth in ref.items():
        F = np.load(pth).astype(np.int64); p, h, d, ok = decompose(F, G)
        isPD = bool(np.array_equal(p, G.inv) and np.array_equal(d, d0))
        rec = {'path': os.path.relpath(pth, APN), 'array_int64_sha256': sha_arr(F), 'form_ok': ok, 'p_is_inverse': bool(np.array_equal(p, G.inv)),
               'd_is_d0': bool(np.array_equal(d, d0)), 'certificate_applies': isPD, 'h_values': h.tolist()}
        if isPD:
            rec.update(analyse(G, p, h, d, full_phi=True))
        else:
            P = [psi_all(G, p, h, d, k) for k in range(q)]
            nz = np.array([[np.count_nonzero(P[k][mu]) for mu in range(q)] for k in range(q)])
            rec.update({'psi_zero_keys': int((nz == 0).sum()), 'min_nonzero_c_tau0': int(nz[0::2].min()), 'min_nonzero_c_tau1': int(nz[1::2].min()),
                        'note': 'p not x^-1 (or d != d0): certificate ell not defined; Psi counted directly only'})
        res['m5_tables'][nm] = rec
        print('m5 table', nm, json.dumps({k: v for k, v in rec.items() if k not in ('h_values',)}, default=str)[:900], round(time.time() - t0, 1), flush=True)
        json.dump(res, open(outp, 'w'), indent=1, default=str)
    res['time_s'] = round(time.time() - t0, 1)
    json.dump(res, open(outp, 'w'), indent=1, default=str); print('DONE', res['time_s'], flush=True)


if __name__ == '__main__':
    main(sys.argv[1])
