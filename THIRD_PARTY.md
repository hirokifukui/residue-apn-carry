# Third-party material

Status: version 1.0.1 (2026-10-13).

## Redistributed in this package

None. Every file listed in `FILE_RIGHTS.tsv` is the author's own work (MIT for code, Lean sources, checkers,
evidence scripts and recorded outputs, and machine-readable metadata; CC BY 4.0 for the paper and the Markdown
documents). The checkers and evidence scripts were written for this project and import only the Python standard
library, NumPy and (two evidence scripts) SymPy. No third-party data tables, papers or fonts are included.

## Dependencies (obtained by the user, not redistributed)

| component | role | licence | how it is obtained |
|---|---|---|---|
| Lean 4 toolchain v4.31.0-rc1 | kernel / compiler | Apache-2.0 | `elan`, pinned by `lean/lean-toolchain` |
| Mathlib, commit d568c8c09630de097a046763c17b9ea99f95f950 | Lean library imported by every module | Apache-2.0 | a checkout at that commit (`lean/lakefile.toml` pins it for Lake; the recorded build used `lean/build_closure.sh` against an existing checkout, see `lean/LEAN_RECORD.md`) |
| zsh | runs `lean/build_closure.sh` | MIT-like (zsh licence) | user's installation |
| Python 3 (>= 3.10) | runs the checkers and evidence scripts | PSF licence | user's installation |
| NumPy | array arithmetic | BSD-3-Clause | user's installation |
| SymPy | exact arithmetic in two evidence scripts | BSD-3-Clause | user's installation |
| pdfTeX / TeX Live, amsart, amsmath, amssymb, booktabs, url, hyperref | builds the public PDF | LPPL and related free licences | user's TeX installation |

The licence names above are the usual licences of these projects; they matter only if a later version
redistributes any of them, which this package does not.

## Used only for the anonymous journal submission build (not in this package)

`iacrtrans.cls` (CC0 1.0 Universal; with its `COPYING` and provenance note) builds the anonymous version of the
paper. It is kept with the anonymous sources, not here.

## Not redistributed

- Cited papers and their PDFs. They are cited, not copied.
- The two earlier papers of the author are cited by their own archive identifiers; their files are not included.
- Internal review packages, hand-off notes, author-check sheets and the private history of failed runs.
