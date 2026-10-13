# evidence/pf -- Proposition pf (author DDT -> integer Walsh = formula)

Paper label(s): `prop:pf`.

## Statement checked (instances)
m=3 (24 576 components) and m=5 (7 864 320 components), 16 tables, wt(rho)=1,2,3.

## Commands (cwd = this directory)
```
python3 -I -B c7/fourier/code/p706_calib.py 3 2 OUT.json
python3 -I -B c7/fourier/code/p706_calib.py 5 2 OUT.json
```

## Expected output
expected/c7/fourier/logs/p706_m3.log and p706_m5.log (8 tables each; n_coeff_compared 3072 resp. 983040 per table; fiber_values_nonzero [0, 4]; max_abs_rhs_nonzero 4).

## Runtime
about 15 s.

## Notes
fr_lib.py imports c5/a1/code/a1c5_lib.py and c1/code/ddt.py by relative path (included).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh pf` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
