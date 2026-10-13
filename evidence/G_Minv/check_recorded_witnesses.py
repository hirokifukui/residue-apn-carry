#!/usr/bin/env python3
"""check_recorded_witnesses.py -- re-verify the RECORDED adversarial witnesses of a_adv.py (mode m3) without re-running
the hill-climbing search (added in version 1.0.1; the historical a_adv.py and its recorded outputs are unchanged).

Why: a_adv.py accepts a hill-climbing step when a floating-point norm satisfies v >= cur; ties and near-ties can be broken
differently on other NumPy versions, so a re-run of the SEARCH may end at a different witness h (with the same headline
maximum). The finite claim of the paper is about the recorded witnesses, so the standard check recomputes every recorded
trial from its stored data (p, K, eps, h) with the unchanged audit library acore.py and compares all recorded fields.

Usage: python3 -I -B check_recorded_witnesses.py RECORDED_a_adv_m3.json OUT.json
Exit 0 iff for every trial: M (integer) equal; MG2, ME2, MZ2, tau2, ratio, bound, tau2_claim_bound equal to relative 1e-9
(absolute 1e-12); ok recomputed equal to the recorded ok and true; every value finite; and the maximum ratio equals the
recorded maximum. Any mismatch, missing field or non-finite value gives exit 1.
"""
import json, math, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c8', 'r1', 'audit_code'))
from acore import GF, ddt_B, physical_blocks, M_count, pd_check  # noqa: E402

FLOATS = ('MG2', 'ME2', 'MZ2', 'tau2', 'ratio', 'bound', 'tau2_claim_bound')


def close(a, b):
    return math.isfinite(a) and math.isfinite(b) and abs(a - b) <= max(1e-12, 1e-9 * max(abs(a), abs(b)))


def main(src, out):
    rec = json.load(open(src))
    F = GF(3); q = F.q
    bad, rows, worst = [], [], 0.0
    for r in rec:
        p, K, h = np.array(r['p']), np.array(r['K']), np.array(r['h'])
        eps = int(r['eps'])
        rho = pd_check(F, p, K, eps); d = eps ^ K
        M = M_count(F, p, d, K, rho)
        tau, nG, nE, nZ = physical_blocks(F, ddt_B(F, p, d, h), rho)
        new = dict(M=int(M), MG2=float(nG ** 2), ME2=float(nE ** 2), MZ2=float(nZ ** 2), tau2=float(tau ** 2),
                   ratio=float(nG ** 2 * q / M), bound=float(M / q),
                   tau2_claim_bound=float((M + 3) / q + (q / 2 - 1) / q ** 2))
        new['ok'] = bool(new['MG2'] <= M / q + 1e-12 and new['ME2'] <= 3 / q + 1e-12
                         and abs(new['MZ2'] - (q / 2 - 1) / q ** 2) < 1e-12)
        diffs = []
        if new['M'] != r.get('M'):
            diffs.append('M')
        for k in FLOATS:
            if k not in r or not isinstance(r[k], (int, float)) or not close(float(r[k]), new[k]):
                diffs.append(k)
        if new['ok'] is not True or r.get('ok') is not True:
            diffs.append('ok')
        if diffs:
            bad.append((r.get('trial'), diffs))
        worst = max(worst, new['ratio'])
        rows.append(dict(trial=r.get('trial'), recomputed=new, mismatches=diffs))
    rec_worst = max(float(r['ratio']) for r in rec)
    ok = not bad and close(worst, rec_worst) and len(rec) > 0
    json.dump(dict(trials=len(rec), mismatching_trials=bad, max_ratio_recomputed=worst, max_ratio_recorded=rec_worst,
                   result='PASS' if ok else 'FAIL', rows=rows), open(out, 'w'), indent=1)
    print('trials', len(rec), 'mismatching', len(bad), 'max ratio recomputed', repr(worst), 'recorded', repr(rec_worst))
    print('WITNESS_CHECK=' + ('PASS' if ok else 'FAIL'))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1], sys.argv[2]))
