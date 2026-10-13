# evidence/G_Minv -- Theorem G and Proposition Minv (two independent implementations)

Paper label(s): `thm:G, prop:Minv`.

## Statement checked (instances)
m=3: 16, m=5: 21 tables; adversarial h (hill climbing); M for p=x^{-1}, m=3..11.

## Commands (cwd = this directory)
```
python3 -I -B c8/r1/code/t1_verify.py c8/r1/code OUT.json
python3 -I -B c8/r1/code/t2_analyze.py c8/r1/code OUT.json 3
python3 -I -B c8/r1/code/t3_extra.py c8/r1/code OUTDIR msurvey
python3 -I -B c8/r1/audit_code/a_main.py OUT.json 3
python3 -I -B c8/r1/audit_code/a_msurvey.py OUT.json
python3 -I -B c8/r1/audit_code/a_adv.py OUT.json m3 11 40
```

## Expected output
expected/c8/r1/audit_results/a_main_m3.log (16 tables, g_eq_PsiSigma, closed_form_ok, MZ2_exact), a_adv_m3.log ("max ratio ||M_G||^2 q / M = 0.4628..."), a_adv_m5_long.log (max ratio 0.0639 <= 0.064, recorded only), a_main_m5.log (21 tables, recorded only), expected/c8/r1/results/t3_msurvey.log (inv: first two entries = d0 type: 2, 4, 5, 5, 5 for m=3..11).

## Runtime
about 3 min (a_adv m3 about 140 s). Not re-run: a_main 5 (8 min recorded), a_adv m5 (2-11 min), t2 m5, t3 adv/bframe/m7/split5.

## Notes
Two recorded files are withheld (hash only in MANIFEST.tsv) because they contain a build-host path: results/commands.json (command list with exit codes) and audit_results/a_adv_m5_run1_exit1.log (a first m=5 attempt that exited 1 through a harness error; rerun with exit 0). Neither is compared by rep.sh. code/ = author implementation (gcore), audit_code/ = independent audit implementation (acore).

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh G_Minv` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
