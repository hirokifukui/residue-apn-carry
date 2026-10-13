# evidence/V3 -- Theorem V(3) (RP law = RF | D)

Paper label(s): `thm:V (3)`.

## Statement checked (instances)
M=5, Q=3, all 120 permutations; exact bounds for m3w2, m5w2, m5w4.

## Commands (cwd = this directory)
```
python3 -I -B c5/attack/code/atk_selftest_v2.py OUT.json   # builds the C5 tables p607 compares against
python3 -I -B c6/attack/code/p607_rp_cond_v2.py OUT.json    # exit 0, P607=PASS
```

## Expected output
expected/c6/attack/logs/p607_rp_cond_v2.log; expected/c6/attack/results/p607_rp_cond_v2.json key "tiny": RP_equals_RF_given_D true, P_RF(D) 12/25.

## Runtime
a few seconds.

## Notes
c6/attack/code/atk_common.py is byte-identical to c5/attack/code/atk_common.py.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh V3` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
