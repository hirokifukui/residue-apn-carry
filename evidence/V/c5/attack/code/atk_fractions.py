"""ATK: exact Fractions of the P5-03 bound min(1, N^{(3-s)w} + C(sN,2)/N^w) for the parameters used in this lane and
for the audit's m5 w4 s4 example.  usage: python3 -I -B atk_fractions.py OUT.json"""
import sys, json, math
from fractions import Fraction
rows = []
for (m, w, s, note) in [(5, 4, 4, 'audit example m5 w4 s4'), (5, 2, 4, 'm5 w2 s4'), (5, 2, 5, 'm5 w2 s5'),
                        (3, 2, 3, 'calib m3 w2'), (3, 2, 4, 'calib m3 w2'), (3, 2, 5, 'calib m3 w2'),
                        (3, 3, 4, 'calib m3 w3 (PD h0)'), (2, 4, 3, 'toy m2 w4'), (2, 4, 4, 'toy m2 w4'), (2, 4, 5, 'toy m2 w4'),
                        (2, 2, 4, 'toy m2 w2'), (2, 2, 5, 'toy m2 w2')]:
    N = 4 ** m
    rf = Fraction(N) ** ((3 - s) * w); sw = Fraction(math.comb(s * N, 2), N ** w); rp = rf + sw
    rows.append({'m': m, 'w': w, 's': s, 'N': N, 'note': note, 'RF_term': str(rf), 'switch_term': str(sw),
                 'RP_bound': str(min(Fraction(1), rp)), 'RP_bound_float': float(min(Fraction(1), rp)),
                 'vacuous': rp >= 1, 'advantage_lower_if_true_always_accepts': str(1 - min(Fraction(1), rp))})
json.dump(rows, open(sys.argv[1], 'w'), indent=1)
for r in rows: print(r)
