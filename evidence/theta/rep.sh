#!/bin/sh
# Representative re-run for Remark theta (mixer for general m): inverse identities for all 69 binary irreducible f,
# 2 <= deg f <= 8, and agreement with multiplication by t in GR(4,m) on all pairs for m = 3, 5 (two polynomials each).
. "$TOOLS/rep_lib.sh"
run c3c4c5 0 $PY code/c3c4c5.py
cmpl expected/c3c4c5.log _run/c3c4c5.out
finish
