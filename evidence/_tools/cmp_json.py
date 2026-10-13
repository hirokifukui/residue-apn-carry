"""cmp_json.py -- compare a re-run's JSON output with a recorded/expected JSON file.

usage: python3 -I -B cmp_json.py EXPECTED.json ACTUAL.json [KEY ...]

With KEY arguments only those top-level keys are compared; otherwise the whole document.
Integers, strings, booleans and null must be identical; floats must agree to relative tolerance
1e-9 or absolute tolerance 1e-12 (floating-point norms are auxiliary and may differ in the last
digits between platforms).  Wall-clock fields (sec, _sec, secs, seconds, time_s, wall_s,
literal_seconds, attack_T_wall_s) are ignored.  Exit 0 on agreement, 1 otherwise.
Non-finite numbers (NaN, Infinity, -Infinity) are rejected on either side, at parse time and before every numeric
comparison (version 1.0.1: before, NaN compared as 'no difference'); a non-finite value gives exit 1.
"""
import json
import math
import sys

TIMING = {'sec', '_sec', 'secs', 'seconds', 'time_s', 'wall_s', 'literal_seconds', 'attack_T_wall_s'}


def diff(a, b, path, out):
    if isinstance(b, dict):
        if not isinstance(a, dict):
            out.append(path); return
        for k in sorted(set(a) | set(b), key=str):
            if k in TIMING:
                continue
            diff(a.get(k, '<missing>'), b.get(k, '<missing>'), path + '.' + str(k), out)
    elif isinstance(b, list):
        if not isinstance(a, list) or len(a) != len(b):
            out.append(path); return
        for i, (x, y) in enumerate(zip(a, b)):
            diff(x, y, '%s[%d]' % (path, i), out)
    elif isinstance(a, float) or isinstance(b, float):
        if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, (int, float)) or not isinstance(b, (int, float)):
            out.append(path); return
        if not (math.isfinite(a) and math.isfinite(b)):
            out.append(path + ' (non-finite)'); return
        if abs(a - b) > max(1e-12, 1e-9 * max(abs(a), abs(b))):
            out.append(path)
    elif a != b or type(a) is not type(b):
        out.append(path)


def _reject_constant(name):
    raise ValueError('non-finite JSON constant %s' % name)


def load(path):
    return json.load(open(path, encoding='utf-8'), parse_constant=_reject_constant)


def main(argv):
    try:
        exp = load(argv[1])
        act = load(argv[2])
    except ValueError as e:
        print('DIFF: $ (%s)' % e)
        print('CMPJSON MISMATCH: non-finite value')
        return 1
    keys = argv[3:]
    if keys:
        exp = {k: exp[k] for k in keys}
        act = {k: act.get(k, '<missing>') for k in keys}
    out = []
    diff(act, exp, '$', out)
    for p in out[:20]:
        print('DIFF:', p)
    print('CMPJSON %s: %d differing fields' % ('OK' if not out else 'MISMATCH', len(out)))
    return 0 if not out else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
