#!/usr/bin/env python3
"""test_cmp_json.py -- positive and negative tests of cmp_json.py (added in version 1.0.1).
Usage: python3 -I -B test_cmp_json.py   (run from anywhere; uses a temporary directory). Exit 0 iff every case behaves as expected."""
import json, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
CASES = [  # (expected document text, actual document text, expected exit)
    ('{"x": 7}', '{"x": 7}', 0),
    ('{"x": 7}', '{"x": 8}', 1),
    ('{"x": 7}', '{"x": NaN}', 1),
    ('{"x": 7}', '{"x": Infinity}', 1),
    ('{"x": 7}', '{"x": -Infinity}', 1),
    ('{"x": NaN}', '{"x": NaN}', 1),
    ('{"x": 0.1}', '{"x": 0.10000000000001}', 0),
    ('{"x": 0.1}', '{"x": 0.1000001}', 1),
    ('{"x": [1, 2.5, "a", true]}', '{"x": [1, 2.5, "a", true]}', 0),
    ('{"x": true}', '{"x": 1}', 1),
    ('{"x": 1, "secs": 3}', '{"x": 1, "secs": 99}', 0),
]
fails = 0
with tempfile.TemporaryDirectory() as d:
    for i, (e, a, want) in enumerate(CASES):
        pe, pa = os.path.join(d, 'e%d.json' % i), os.path.join(d, 'a%d.json' % i)
        open(pe, 'w').write(e); open(pa, 'w').write(a)
        rc = subprocess.run([sys.executable, '-I', '-B', os.path.join(HERE, 'cmp_json.py'), pe, pa],
                            capture_output=True).returncode
        ok = rc == want
        fails += not ok
        print('%s case %d expected=%s actual=%s exit=%d want=%d' % ('PASS' if ok else 'FAIL', i, e, a, rc, want))
print('TEST_CMP_JSON=%s (%d cases, %d failed)' % ('PASS' if not fails else 'FAIL', len(CASES), fails))
sys.exit(1 if fails else 0)
