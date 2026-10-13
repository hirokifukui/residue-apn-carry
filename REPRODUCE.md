# REPRODUCE

All commands are run from the repository root unless stated otherwise. Each command exits non-zero on failure.
Requirements: Python 3 (>= 3.10) with NumPy and SymPy; pdfTeX (TeX Live); for Lean, `elan` and zsh.

## Integrity and Blueprint
```
shasum -a 256 -c SHA256SUMS
python3 -I -B tools/check_blueprint.py . --labels-file paper/LABELS.tsv
```
Expected: every file OK; `BLUEPRINT rows=28 failures=0`. With `--labels-file` the theorem numbers in `BLUEPRINT.md` are
checked against `paper/LABELS.tsv`, the label list generated from the .aux file of the build of the PDF (the tool reads that
list, not the PDF itself); without it the labels are read from `paper/*.tex`.

## Paper
```
cd paper
for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error main_v15.tex; done
```
Expected: three exits 0; 43 pages; no overfull boxes; no undefined references.

## Finite checks
Three checkers with expected outputs:
```
python3 -I -B checks/p802_zexact.py  out_p802.json
python3 -I -B checks/p803_steps_v2.py out_p803.json
python3 -I -B checks/p805_p806.py    out_p805.json
python3 -I -B checks/p803_steps_v2.py out_fault.json --fault-C1   # must exit 1 (negative control)
```
Expected outputs are in `checks/expected/`. Exact integer/rational fields must agree; floating-point norms are
auxiliary and may differ in the last digits between platforms.

All rows of the finite-check and cost tables of Section 7 (and Remark 7.1), one representative re-run per row:
```
sh run_all_representatives.sh            # all rows, about 10 minutes on 2 cores
sh run_all_representatives.sh eps UE     # selected rows; 'public' = the three checkers above
sh run_all_representatives.sh selftest   # tests of the comparison helper (NaN/Infinity are rejected)
G_MINV_SEARCH=1 sh run_all_representatives.sh G_Minv   # optionally also re-run the adversarial search of Theorem 6.4
```
Each row runs in a temporary copy of `evidence/<row>/` with an empty HOME and compares with the recorded output
(`evidence/<row>/expected/`). Exit 0 iff every executed command had its expected exit code and every comparison
agreed. For Theorem 6.4 (m = 3) the standard check recomputes the 40 recorded adversarial witnesses
(`evidence/G_Minv/check_recorded_witnesses.py`); the hill-climbing search accepts floating-point ties and may end at
different witnesses on other NumPy versions, so its optional re-run is reported, not compared. `EVIDENCE_COVERAGE.tsv` lists, per table row, the scripts, the recorded outputs and the rows that rest on the
recorded output only. The scripts are the historical ones, byte-identical (hashes and origins in each
`evidence/<row>/MANIFEST.tsv`); their docstrings keep the internal round labels of the project.

## Lean 4
Toolchain `leanprover/lean4:v4.31.0-rc1` (`lean/lean-toolchain`); Mathlib commit
`d568c8c09630de097a046763c17b9ea99f95f950` (`lean/lakefile.toml`). Check the pin of your Mathlib checkout first:
`git -C /path/to/mathlib rev-parse HEAD` must print that commit.

Source-only build used for the record (zsh; one `lean` invocation per module, import order, stops at the first
failure; needs an empty `lean/build/`):
```
cd lean
CHECK_MATHLIB=/path/to/a/mathlib/checkout/at/that/commit zsh ./build_closure.sh
cat logs/RESULT.txt          # expected: OK 26 modules + root
```
The recorded run of this script is in `lean/record/` (per-module exit codes, `#print axioms` output of the
`Axioms*.lean` modules, source hashes before and after) and summarized in `lean/BUILD_RECORD.txt` and
`lean/LEAN_RECORD.md`. With Lake (not run for this record): `cd lean && lake exe cache get && lake build`.
