# evidence/UE -- Theorem UE (energy identity; calE_Z, calE_B)

Paper label(s): `thm:UE`.

## Statement checked (instances)
m=5: 11 tables (incl. wt(rho)=2,3); m=7: 8 tables (incl. wt(rho)=4).

## Commands (cwd = this directory)
```
python3 -I -B c1/code/t303_oracle.py c1/data; python3 -I -B c1/code/t311a_rowmax.py c1/data OUT.json
python3 -I -B c3/a1/code/a1_lifts.py; python3 -I -B c3/a1/code/a1_gpair.py 5
python3 -I -B c5/a1/code/a1c5_ue.py 5   # exit 0
python3 -I -B c5/a1/code/a1c5_ue.py 7   # exit 0
```

## Expected output
expected/c5/a1/logs/a1c5_ue_m5.log ("calE_Z": "211/512" in every table, calE_B_float 3.4973 .. 3.5588, identity_checked_all_G_u true), expected/c5/a1/logs/a1c5_ue_m7.log ("calE_Z": "2059/8192", calE_B_float 3.3453 .. 3.3571).

## Runtime
about 2 min (m=7 about 80 s).

## Notes
a1_lifts.py, a1_gpair.py and a1c5_ue.py hard-code `~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher`; handled by `home_link` (throwaway HOME only). a1c5_ue.py writes its JSON to c5/a1/results/ (rep.sh creates the directory).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh UE` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
