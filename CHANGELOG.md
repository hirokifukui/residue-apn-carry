# CHANGELOG

## 1.0.0 (2026-10-13, first public release)
- First public release. New repository and new archive records for this third paper of the series (the earlier papers keep their own
  repositories and records; they are cited, not earlier versions of this work).
- Finite checks: `evidence/` holds the scripts, inputs and recorded outputs behind every row of the finite-check and
  cost tables of Section 7 and the check of Remark 7.1; `EVIDENCE_COVERAGE.tsv`; `run_all_representatives.sh`.
- Paper: Data and code availability states exactly what is provided and which rows rest on recorded outputs only;
  the second earlier paper is cited by its paper record (not its software record); layout of three tables and one
  display (no change of content).
- Lean: unchanged sources; `lean/record/` and `lean/LEAN_RECORD.md` connect the released sources to the recorded build.
- Licences: unchanged split (code MIT, prose CC BY 4.0); `CITATION.cff` no longer states a single top-level licence.

## 0.9.0-rc1 (release candidate, not published)
- Paper: the optimal exponent 1/2 is stated only for the inverse map with d = 1 + K0(x/rho), K0 = X^4 + X^2, m odd;
  general linearized degree e with its constant; Table 1 of quantifiers; bibliography completed (Baigneres-Vaudenay
  pages and DOI); author block, data availability and AI-use statements.
- Lean: the two-word mixer is an additive automorphism (MixAdd, ThetaZ4_v3, non-empty witness m = 5); the former
  pointwise-ring specialization is shown vacuous (VacuousZ4); one source closure that builds from sources only.
- Checks: `p803_steps_v2.py` asserts all three parts (A, B, C) and rejects a wrong constant.
