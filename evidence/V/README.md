# evidence/V -- Theorem V (decomposition of the candidate-existence test)

Paper label(s): `thm:V`.

## Statement checked (instances)
toy m=2, w=2: all 16 777 216 theta, 32 cases; m=3 sample of 58 035.

## Commands (cwd = this directory)
```
python3 -I -B c5/attack/code/atk_selftest_v2.py OUT.json        # builds the small tables in c5/attack/results/data
python3 -I -B c5/attack/code/atk_runs_v2.py literal OUT.json F_toy_m2 2 2 4 E:0,RF:0,RP:0   # 3 of the 32 cases
python3 -I -B sum_m3_sample.py expected/c5/attack/results/ATK_SUMMARY.json   # recount 58 035 from the aggregate
```

## Expected output
expected/c5/attack/logs/p503_literal_m2w2.log and p503_toy2.log (32 cases, sets_equal True in each); the m=3 sample (58 035 literal-versus-factorized evaluations, 0 disagreements) is recorded in the aggregate expected/c5/attack/results/ATK_SUMMARY.json under true/p510v2_true_F_nat_m3_X1_X3_X9.json, true/p510v2_true_F_pd_m3_inv_a3.json and true/p510v2_true_F_pd_m3_inv_h0.json (by_s.*.literal_vs_factorized_checked: 19 344 + 19 339 + 19 352; recorded only; the three source result files are not in this package). `sum_m3_sample.py` recomputes the total from the aggregate.

## Runtime
about 1 min for the 3 cases (each literal case enumerates all 16^6 theta). The other 29 toy cases and the m=3 random runs are REUSED_RECORD.

## Notes
Version 1.0.1: the pointer for the m=3 count was corrected (version 1.0.0 named the p503_rand* runs); the total is now recomputed from the recorded aggregate by `sum_m3_sample.py`. This is a recount of recorded results, not a re-run of the 58 035 evaluations.

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
