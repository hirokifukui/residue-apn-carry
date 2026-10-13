# evidence/cost_p413 -- Cost table rows 1-3: three-round Feistel x^3 75 AND, S2 natural 145 AND, S2 inverse-based PD 235 AND

Paper label(s): `tab:cost`.

## Statement checked (instances)
bit-model counts, m=5.

## Commands (cwd = this directory)
```
python3 -I -B c4/cost/p413_cost.py c2/cost/p210_results.json c4/spec/CANDIDATE_P4_SPLIT_TAIL.json c3/spec/CANDIDATE_P3B_THREE.json OUT.json
```

## Expected output
expected/c4/cost/p413.log line FEISTEL: "Feistel3_f=x^3": {"AND": 75, ...}, "S2_PD_inv": {"AND": 235, ...}, "S2_natural": {"AND": 145, ...}; exit 0 (p413.exit).

## Runtime
seconds; needs sympy (imported at top level). Not re-run in the evidence lane (sympy unavailable there): REUSED_RECORD.

## Notes
The 4/N column is a cited theorem (AO, Thm 2) or Theorem W2, not a computation.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh cost_p413` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
