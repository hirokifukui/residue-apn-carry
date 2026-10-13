# evidence/V -- Theorem V (decomposition of the candidate-existence test)

Paper label(s): `thm:V`.

## Statement checked (instances)
toy m=2, w=2: all 16 777 216 theta, 32 cases; m=3 sample of 58 035.

## Commands (cwd = this directory)
```
python3 -I -B c5/attack/code/atk_selftest_v2.py OUT.json        # builds the small tables in c5/attack/results/data
python3 -I -B c5/attack/code/atk_runs_v2.py literal OUT.json F_toy_m2 2 2 4 E:0,RF:0,RP:0   # 3 of the 32 cases
```

## Expected output
expected/c5/attack/logs/p503_literal_m2w2.log and p503_toy2.log (32 cases, sets_equal True in each); the m=3 sample (58 035 literal evaluations, 0 mismatches) is in the p503_rand* logs/results (recorded only).

## Runtime
about 1 min for the 3 cases (each literal case enumerates all 16^6 theta). The other 29 toy cases and the m=3 random runs are REUSED_RECORD.

## Notes
The m=3 count 58 035 is a sum over the recorded rand runs as stated in the attack notes; the evidence lane did not re-derive the sum from the JSON files.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh V` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
