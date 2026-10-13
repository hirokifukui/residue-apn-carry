# evidence/eps -- Theorem eps (Delta(B) = q for every coefficient lift h)

Paper label(s): `thm:eps`.

## Statement checked (instances)
m=5: natural, h=0, adversarial G lift, three random h; m=7: r=3 and r=5 with natural, h=0, three random h; m=5 with wt(rho)=3,3,5 (synthetic d).

## Commands (cwd = this directory)
```
python3 -I -B c1/code/t303_oracle.py c1/data            # builds F_m5_r3.npy, F_m7_r5.npy, F_m7_r3.npy (exit 0)
python3 -I -B c1/code/t311a_rowmax.py c1/data OUT.json # builds F_m5_r3_adversarialG.npy (exit 0)
python3 -I -B c2/code/p202_epsilon.py c1/data OUT.json 5 F_m5_r3 F_m5_r3_adversarialG   # exit 0
python3 -I -B c2/code/p202b_general_rho.py c1/data OUT.json                            # exit 0
```

## Expected output
expected/c2/logs/p202_m5.log (DU_B 32 for all 6 variants, Z_bound_violations 0), expected/c2/logs/p202b.log (rho 7, 21, 31; DU_B 32).

## Runtime
about 30 s for the representative commands. Not re-run here: m=7 (`... 7 F_m7_r3`, `... 7 F_m7_r5`, about 30 s each; recorded in expected/c2/logs/p202_m7_r*.log, exit 0). A first combined m=7 invocation recorded EXIT=1 (script assumption, rerun per r) and is not included.

## Scope
Finite calibration, not a proof. These computations check the stated instances only; the general statements are
proved on paper in the sections cited.

## How to run
From the repository root: `sh run_all_representatives.sh eps` (copies this directory to a temporary directory,
sets HOME to an empty temporary directory, runs `rep.sh` with `python3 -I -B`, and compares with `expected/`).
Comparison rules: integers, strings and booleans must agree exactly; floating-point values to relative 1e-9
(they are auxiliary); wall-clock fields are ignored (`_tools/cmp_lines.py`, `_tools/cmp_json.py`).

## Files
`MANIFEST.tsv` lists every file with its SHA-256 and the private source path it was copied from (byte-identical).
Scripts are the historical author/audit scripts, unedited; paths inside them are relative to this directory
(the layout `c1/ ... c8/` reproduces the original tree), except where noted below.
`expected/` holds the recorded logs, exit files and JSON results of the original runs.
