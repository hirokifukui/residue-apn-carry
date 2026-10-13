# TRUST: what supports each claim

This package accompanies the paper *Carry-aware differential bounds and certified correction of local zero sums*
(`paper/main_v15.pdf`). It separates four kinds of support. Nothing here is a security claim for a concrete cipher.

1. **Paper proofs.** Every theorem of the paper is proved in the paper (Sections 2-6, Appendix A). This is the
   primary support. Statements and their proofs are listed in `BLUEPRINT.md`.
2. **Lean 4 (parts checked in Lean).** `lean/` contains the complete source closure of the formalized parts
   (27 modules incl. the root). It was built from sources only against Lean 4.31.0-rc1 and Mathlib
   `d568c8c09630de097a046763c17b9ea99f95f950` (`lean/build_closure.sh`); every printed declaration depends only on
   `propext`, `Classical.choice`, `Quot.sound` or on no axiom. No `sorry`, no `native_decide`, no new axiom.
   The summary is `lean/BUILD_RECORD.txt`; the raw per-module exit codes, axiom listings and source hashes of that run
   are in `lean/record/`, and `lean/LEAN_RECORD.md` shows that the source hashes of the run equal the released files.
   A Lean entry covers exactly the scope stated in `BLUEPRINT.md` (e.g. weight-one kernel direction, w = 2). In the
   final two-word statement the one-round data (p, K, epsilon) enter as hypotheses; the mixer hypotheses are
   instantiated (m = 5).
3. **Finite calibration.** `checks/` contains three checkers with expected outputs; `evidence/` contains, for every
   other row of the finite-check and cost tables of Section 7 and for the check of Remark 7.1, the unedited scripts
   that produced the printed numbers, their inputs (or the scripts that rebuild them) and the recorded logs, exit codes
   and results. `EVIDENCE_COVERAGE.tsv` says, row by row, what is re-run by `run_all_representatives.sh` and what rests
   on the recorded output only (the m = 7 instances of Theorems 3.4 and 6.2, the m = 5 instances of Theorem 6.4 and
   Proposition 6.5, 29 of the 32 toy cases and the m = 3 sample of Theorem 5.7). For the adversarial search of Theorem 6.4
   (m = 3) the standard check recomputes the 40 recorded witnesses; re-running the floating-point search is optional
   (`G_MINV_SEARCH=1`). These checks test instances; they do not prove the general statements. `checks/p803_steps_v2.py` fails (non-zero exit) on an injected wrong constant
   (`--fault-C1`).
4. **Cited results.** Results of other papers are used as stated there (references in the paper).

## Known limits of the formal part
- The two-word mixer is formalized as an additive automorphism (x, y) -> (x + y, x + Theta y) of
  ((Z/4)^m)^2 with Theta and Theta - I invertible; a witness is given for m = 5. That this is the mixer
  [[1,1],[1,t]] of GR(4,m) is Remark 7.1 of the paper (proof on paper; exact finite checks for 2 <= deg f <= 8 in
  `evidence/theta/`).
- An earlier formal specialization that took the mixer entries in the pointwise ring (Z/4)^m had unsatisfiable
  hypotheses; this is proved in `lean/ApnCipher/VacuousZ4.lean`, and that specialization is not counted.
- Not formalized: general omega (Theorem 3.7(2)), Theorem 3.9, general w, Section 6, the power sums of Section 4,
  the identification of GR(4,m) multiplication with the companion matrix (paper).

## What was not done
No second-machine Lean build, no lean4checker replay, no `lake build` from a fresh Mathlib download (the closure was
built against an existing Mathlib checkout pinned to the commit above). The long historical runs listed in item 3 are
not repeated; their scripts and recorded outputs are included.
