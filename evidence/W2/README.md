# evidence/W2 -- Theorem W2 (exact N*EDP_2, m = 5, author DDT, integer matrix products)

Paper label(s): `thm:W2`.

## Statement checked (instances)
natural 185/128, h=0 311/128, adversarial 31/16, random h 303/256 (p301); x^{-1} with d0 (ring-polynomial witness) 159/128 and the wt(rho)=3 example 75/64 (p312).

## Commands (cwd = this directory)
```
python3 -I -B c1/code/t303_oracle.py c1/data
python3 -I -B c2/cost/p210_hermite_cost.py c2/cost   # writes the H_A/H_B/P1theta tables read by p312 (about 80 s)
python3 -I -B c3/pd/p312_pd_roles.py c3/pd           # 159/128, 75/64, 185/128, 311/128 (exit 0)
python3 -I -B c3/code/p301_warmstart.py . OUT.json   # needs sympy, and the c3/a1 lift tables (rep.sh builds them)
```

## Expected output
expected/c3/pd/p312.log (CHECK X30_d0_ringpoly ... "2": ["159/128"; CHECK mainp_rho=wt3_randh ... "2": ["75/64"), expected/c3/logs/p301.log ("N_EDP_t2": "185/128", "311/128", "31/16", "303/256").

## Runtime
about 2 min. p301_warmstart.py imports sympy at top level; where sympy is absent rep.sh reports NOT_RUN for it and the four p301 values rest on the recorded output (exit 0).

## Notes
c3/a1/code/a1_lifts.py and a1_gpair.py hard-code `~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher`; rep.sh does not edit them but links that path inside the throwaway HOME to this directory (`home_link` in _tools/rep_lib.sh).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh W2` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
