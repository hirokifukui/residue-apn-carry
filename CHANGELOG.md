# CHANGELOG

## 1.0.1 (2026-10-13)
Corrections after the post-publication audits of 1.0.0 (no change of any theorem, proof or Lean source):
- Paper: Table 5 states the adversarial-search values of Theorem 6.4 as the largest observed floating-point values
  0.46287 (m = 3) and 0.06390 (m = 5); 1.0.0 printed "<= 0.46" for m = 3, which the recorded maximum 0.46286958505344594
  exceeds. "machine-checked" is replaced by "checked in Lean" (Section 7). Data and code availability cites the concept DOI
  of the software record (all versions) and describes the witness re-verification below.
- Evidence: `evidence/G_Minv/check_recorded_witnesses.py` re-verifies the 40 recorded witnesses of the adversarial search
  (standard check); re-running the search is optional (`G_MINV_SEARCH=1`), because floating-point ties can lead to
  different witnesses on other NumPy versions. `_tools/cmp_json.py` rejects NaN/Infinity (with `_tools/test_cmp_json.py`,
  row `selftest`). `evidence/V`: the pointer for the m = 3 sample 58 035 is corrected and the total is recounted from the
  recorded aggregate (`sum_m3_sample.py`).
- Documents: Blueprint names the current paper source; REPRODUCE explains that `--labels-file` reads `paper/LABELS.tsv`;
  the CC BY notice and its row in FILE_RIGHTS.tsv describe it as the author's licence notice with a link to the legal code.
- Historical scripts and their recorded outputs are unchanged (hashes in each `evidence/<row>/MANIFEST.tsv`).

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
