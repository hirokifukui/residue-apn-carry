# evidence/general_d -- General d: Lemma norm, Theorems top..repair, Proposition affine (also the g_d circuit of the cost table)

Paper label(s): `lem:norm, thm:top--thm:repair, prop:affine`.

## Statement checked (instances)
m=3,4,5; 19 maps d (random rho, hyperplane and K, plus d0); coefficients for 144/144/168 keys; all L and mu for m=3 (45 056 keys); chi two choices; 550 affine h (40 per d for m=3,4; 10 per d for m=5).

## Commands (cwd = this directory)
```
python3 -I -B c7/gd/code/p702.py OUT.json
python3 -I -B c7/gd/code/p703.py OUT.json
python3 -I -B c7/gd/code/p704.py OUT.json
python3 -I -B c7/gd/code/p705.py OUT.json
```

## Expected output
expected/c7/gd/logs/p703.log (min_nonzero_deg_s1 6/13/28, min_nonzero_deg_s2 7/12/28, exhaustive_m3_keys 45056 ok 45056); p704.log (ANF coordinate degree max 2; pass rates 0.8733..0.8791); p702.log (19 d, PASS True); p705.log (circuit, local comparison).

## Runtime
under 10 s for all four.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh general_d` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
