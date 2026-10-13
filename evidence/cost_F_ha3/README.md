# evidence/cost_F_ha3 -- Cost table row 4: one F, PD table with h=a^3: 75 AND, 98 XOR, 1 NOT

Paper label(s): `tab:cost`.

## Statement checked (instances)
explicit gate DAG for m=5 (and m=7), evaluated on all inputs against reference tables.

## Commands (cwd = this directory)
```
python3 -I -B run_author_only.py expected/c5/pd/results/pd5_circuit_v2.json OUTDIR   # exit 0, AUTHOR_ONLY=PASS
```
`run_author_only.py` is a new wrapper. It imports the unedited module `c5/pd/code/pd5_circuit_v2.py` and calls its
`build()`, `eval_table()` and `DAG.counts()`, writes the DAG in the format of `main()`, compares every evaluated table
with the author reference tables (c5/pd/data/F_PD_{h0,hX3}_m{5,7}.npy, c4/pd/data/F_pd_inv_m5.npy), and checks gate
counts, chain-only counts, the table hash and the DAG-file hash against the recorded JSON. The script's own `main()` is
not used because it additionally compares the m=5, h=a^3 table with an external auditor table; that comparison is a
cross-check only and does not enter the counts.

## Expected output
expected/c5/pd/logs/pd5_circuit_v2.log line "5 True {'AND': 75, 'XOR': 98, 'NOT': 1, ...}"; exit 0.

## Runtime
Under 1 s. The external auditor table is not included; reference only: the recorded run reports it equal to the
author table F_PD_hX3_m5.npy (field "match" in expected/c5/pd/results/pd5_circuit_v2.json).

## Notes
pd5_circuit_v2.py, pd5_math.py (unedited) and the recorded log/JSON still contain the path of the auditor package
directory under gpt_input/ (a path string only; no auditor file is included).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh cost_F_ha3` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
