"""cmp_lines.py -- compare a re-run's stdout with lines taken verbatim from the recorded log.

usage: python3 -I -B cmp_lines.py EXPECTED_LINES ACTUAL_STDOUT

Every non-empty line of EXPECTED_LINES must match a line of ACTUAL_STDOUT, in the same order
(other lines in ACTUAL_STDOUT are allowed).  Two lines match when, after removing wall-clock
timing fields, their text outside numbers is identical, every integer is identical, and every
floating-point number agrees to relative tolerance 1e-9 (absolute 1e-12).  Removed timing fields:
values of keys sec, _sec, secs, seconds, literal_seconds, attack_T_wall_s, time_s, wall_s, and trailing
elapsed-time numbers after a closing bracket or PASS/DONE at the end of a line
(e.g. 'P312=PASS 2.0', 'DONE 30.1', '...} 29s').
Exit 0 if all expected lines are found, 1 otherwise.
"""
import re
import sys

TIMING_KEY = re.compile(r"""(["']?(?:sec|_sec|secs|seconds|literal_seconds|attack_T_wall_s|time_s|wall_s)["']?\s*:\s*)[-+0-9.eE]+""")
TRAIL = re.compile(r"([}\])]|PASS|DONE)(?:\s+[0-9]+(?:\.[0-9]+)?s?)+\s*$")
NUM = re.compile(r"[-+]?(?:\d+\.\d*|\.\d+|\d+)(?:[eE][-+]?\d+)?")


def norm(line):
    line = TIMING_KEY.sub(r"\1T", line.rstrip("\n"))
    line = TRAIL.sub(r"\1", line)
    return line


def tokens(line):
    text = NUM.split(line)
    nums = NUM.findall(line)
    return text, nums


def same(a, b):
    ta, na = tokens(norm(a))
    tb, nb = tokens(norm(b))
    if ta != tb or len(na) != len(nb):
        return False
    for x, y in zip(na, nb):
        if x == y:
            continue
        isf = any(c in x + y for c in '.eE')
        if not isf:
            return False
        fx, fy = float(x), float(y)
        if abs(fx - fy) > max(1e-12, 1e-9 * max(abs(fx), abs(fy))):
            return False
    return True


def main(exp_path, act_path):
    exp = [l for l in open(exp_path, encoding='utf-8') if l.strip()]
    act = [l for l in open(act_path, encoding='utf-8', errors='replace')]
    j = 0; missing = 0
    for e in exp:
        k = j
        while k < len(act) and not same(e, act[k]):
            k += 1
        if k == len(act):
            missing += 1
            print('MISSING:', e.rstrip()[:200])
        else:
            j = k + 1
    print('CMP %s: %d/%d expected lines matched' % ('OK' if missing == 0 else 'MISMATCH', len(exp) - missing, len(exp)))
    return 0 if missing == 0 else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1], sys.argv[2]))
