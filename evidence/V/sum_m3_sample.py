#!/usr/bin/env python3
"""sum_m3_sample.py -- recompute the m = 3 sample size 58 035 of Theorem V from the recorded aggregate
expected/c5/attack/results/ATK_SUMMARY.json (added in version 1.0.1). The three source result files
p510v2_true_*.json are summarised in ATK_SUMMARY.json and are not themselves part of this package.
Usage: python3 -I -B sum_m3_sample.py ATK_SUMMARY.json    Exit 0 iff the total is 58035 and every disagreement count is 0."""
import json, sys
d = json.load(open(sys.argv[1]))['true']
keys = ['p510v2_true_F_nat_m3_X1_X3_X9.json', 'p510v2_true_F_pd_m3_inv_a3.json', 'p510v2_true_F_pd_m3_inv_h0.json']
total, dis = 0, 0
for k in keys:
    bs = d[k]['by_s']
    c = sum(int(v['literal_vs_factorized_checked']) for v in bs.values())
    x = sum(int(v['literal_vs_factorized_disagree']) for v in bs.values())
    print('%s checked=%d disagree=%d' % (k, c, x))
    total += c; dis += x
print('TOTAL checked=%d disagree=%d' % (total, dis))
sys.exit(0 if (total == 58035 and dis == 0) else 1)
