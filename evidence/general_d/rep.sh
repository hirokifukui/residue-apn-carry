#!/bin/sh
# Representative re-run for general d (Lemma norm, Theorems top..repair, Proposition affine): all four scripts.
. "$TOOLS/rep_lib.sh"
for s in p702 p703 p704 p705; do
  run $s 0 $PY c7/gd/code/$s.py _run/$s.json
  cmpl expected/c7/gd/logs/$s.log _run/$s.out
  cmpj expected/c7/gd/results/$s.json _run/$s.json
done
finish
