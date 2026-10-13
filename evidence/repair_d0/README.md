# evidence/repair_d0 -- Section repair, d0 (power sums, top coefficients, correction rule, m=5 all local keys for h=a^3)

Paper label(s): `sec:repair`.

## Statement checked (instances)
power sums m=3,5,7,9; coefficients 40/40/8 cases (m=3,5,7); correction rule all lambda, 800 pairs; m=5 all 1024 local keys for h=a^3.

## Commands (cwd = this directory)
```
python3 -I -B c6/h/code/h6_check.py OUT.json        # exit 0
python3 -I -B c1/code/t303_oracle.py c1/data       # regenerates c1/data/F_m5_r3.npy (natural table read by pd6_cert)
python3 -I -B c6/pd/code/pd6_cert.py OUT.json        # exit 0; reads c5/pd/data/F_PD_{h0,hX3}_m5.npy, c4/pd/data/F_pd_inv_hC3_m5.npy
```

## Expected output
expected/c6/h/logs/h6_check.log (powersums 1,1,0,1,0 for m=3,5,7,9; coef_cases 40/40/8; repair_checks 160+640=800; ALL_OK true); expected/c6/pd/logs/pd6_cert.log ("m5 hX3 ... min_nonzero_c_tau0": 27, "min_nonzero_c_tau1": 26).

## Runtime
About 10 s in total. The three author reference tables under c5/pd/data and c4/pd/data are byte-identical copies
of the private tree (SHA-256 in MANIFEST.tsv); pd6_cert prints the int64-array SHA-256 of every table it reads, and these
lines agree with the recorded log.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh repair_d0` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
