# evidence/theta -- Remark theta (the mixer for general m)

Paper label(s): `rem:theta`.

## Statement checked (instances)
Theta = matrix of multiplication by t on (Z/4)[t]/(f^) for every binary irreducible f with 2 <= deg f <= 8 (69 polynomials):
inverse identities for Theta and Theta - I modulo 4, determinant formulas; t-multiplication equals the Theta action on all
4^m vectors (m <= 6); the mixer (x, y) -> (x + y, x + Theta y) agrees with [[1,1],[1,t]] over GR(4,m) on all pairs and is
bijective for m = 3 (two f) and m = 5 (two f). Also: in the pointwise ring (Z/4)^m (m = 1, 2) no 2x2 matrix with four unit
entries has a unit determinant (the negative control behind `VacuousZ4`).

## Commands (cwd = this directory)
```
python3 -I -B code/c3c4c5.py      # exit 0, last line TOTAL FAILS: 0
```

## Expected output
`expected/c3c4c5.log` (and `expected/c3c4c5.exit`, recorded exit 0).

## Runtime
about 5 seconds.

## Notes
Written by an audit pass that did not see the derivation (independent code, NumPy only); section names C3/C4/C5 in the
log are the audit's item numbers.

## Scope
Finite calibration, not a proof. The general statement of the remark is proved on paper.

## How to run
From the repository root: `sh run_all_representatives.sh theta`.
