# Carry-aware differential bounds and certified correction of local zero sums

Hiroki Fukui. Version 1.0.1, 2026-10-13.

## Results

We study a two-digit coordinate model of maps on the Galois ring GR(4,m), with q = 2^m and N = q^2 = |GR(4,m)|, in which the ring addition carries from the low digit into the high digit. For maps F(a,b) = (p(a), h(a) ⊕ d(a)b) with p an APN permutation, d a nowhere-vanishing F_2-affine map whose linear part has a one-dimensional kernel, and h arbitrary, we prove direction-wise differential counts for B = J ∘ F, a key-averaged two-block bound of order 1/N, and a collision-energy bound, all uniform in h. In contrast, a local integral property of the same two-block map depends on h; for the inverse map and every admissible d we give a linear certificate on h that excludes a family of local zero sums, and an explicit correction of Boolean degree two of every h that fails it; degree two is minimal for this local problem. For the averaged alternating two-word arrangement we prove a one-word contraction of order q^{-(1-(1/2)log_2 3)}, uniform in h and in the admissible data, and deduce that a fixed number of steps brings the averaged two-word difference distribution to the scale 1/N. For the inverse map with d(a) = 1 + (a/ρ)^4 + (a/ρ)^2, where m is odd and ρ ≠ 0, the contraction improves to the order q^{-1/2}, which is optimal since no admissible data give a faster order; for other d our constant grows with the linearized degree of d. We then record what these statements do and do not imply for an independent-key composition: the averaged multi-word bound coexists with a candidate-existence distinguisher with data linear in the word size. No security claim for a concrete cipher is made.

## Paper

- PDF: `paper/main_v15.pdf` (public named build, 43 pages).
- Sources: `paper/` (`main_v15.tex` and the files it inputs; build with three pdflatex runs, see `REPRODUCE.md`).
- Zenodo paper record, version DOI: https://doi.org/10.5281/zenodo.23333044.
- Zenodo paper record, concept DOI (all versions): https://doi.org/10.5281/zenodo.23330908.

## Verification

- What is proved where (paper, Lean 4, finite calibration, cited result): `TRUST.md` and `BLUEPRINT.md`.
- Lean 4 sources: `lean/` (toolchain pinned in `lean/lean-toolchain`, Mathlib pinned by commit in `lean/lakefile.toml`; source-only build: `lean/build_closure.sh`; build record: `lean/BUILD_RECORD.txt`, `lean/LEAN_RECORD.md`).
- Finite checks: `checks/` (three checkers with expected outputs) and `evidence/` (the scripts, inputs and recorded outputs behind every other row of the finite-check and cost tables of Section 7; index `EVIDENCE_COVERAGE.tsv`; one representative re-run per row: `run_all_representatives.sh`). Commands in `REPRODUCE.md`. Finite checks are calibrations, not proofs.
- File hashes: `SHA256SUMS`.

## Citation

See `CITATION.cff`.
- This source archive, version DOI: https://doi.org/10.5281/zenodo.23333039.
- This source archive, concept DOI (all versions): https://doi.org/10.5281/zenodo.23330906.
- Repository: https://github.com/hirokifukui/residue-apn-carry (tag v1.0.1).

Related earlier papers by the same author (cited works, not earlier versions of this one):
- Optimal reduced representatives of quadratic APN permutations in odd dimension, https://doi.org/10.5281/zenodo.23053113.
- Explicit reduced APN permutations: ramification and optimal Galois-ring lifts, https://doi.org/10.5281/zenodo.23233176.

## Licences

- Code, Lean sources, checkers, evidence scripts and recorded outputs, machine-readable metadata: MIT (`LICENSE`).
- Paper (sources and PDF), Blueprint and other Markdown documents: CC BY 4.0 (`LICENSE-CC-BY-4.0.txt`).
- Per-file licence, role and origin: `FILE_RIGHTS.tsv`; third-party material: `THIRD_PARTY.md`.

Contact: Hiroki Fukui, fukui@somec.org, ORCID https://orcid.org/0009-0008-7122-522X.
