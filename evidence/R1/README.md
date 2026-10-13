# evidence/R1 -- Theorem R1 (block norms; ||M_Z||^2 = (q/2-1)/q^2)

Paper label(s): `thm:R1`.

## Statement checked (instances)
m=3,5,7, 20 tables (8 + 8 + 4); numerical norms.

## Commands (cwd = this directory)
```
python3 -I -B c7/fourier/code/p707_gram.py 3 2 OUT.json
python3 -I -B c7/fourier/code/p707_gram.py 5 2 OUT.json
python3 -I -B c7/fourier/code/p706_calib.py 3 2 OUT.json   # Z-block norms
python3 -I -B c7/fourier/code/p707_gram.py 7 0 OUT.json   # recorded only
```

## Expected output
expected/c7/fourier/logs/p707_m{3,5,7}.log; Z-block value in p706_m*.log norms_W.Z (0.21650635 = sqrt(3/64) for m=3; 0.12103073 = sqrt(15/1024) for m=5).

## Runtime
m=3,5 about 15 s. m=7 is REUSED_RECORD (took 242 s in the evidence lane; integer fields agreed, iteratively computed operator norms agreed to about 1e-8 relative only, i.e. beyond the 1e-9 comparison tolerance).

## Notes
The exactness of ||M_Z||^2 is also checked as the boolean MZ2_exact in G_Minv (a_main, 37 tables).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh R1` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
