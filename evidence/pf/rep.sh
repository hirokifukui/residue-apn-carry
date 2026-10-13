#!/bin/sh
# Representative re-run for Proposition pf (DDT -> integer Walsh vs formula; m = 3 and m = 5, 16 tables).
. "$TOOLS/rep_lib.sh"
for m in 3 5; do
  run p706_m$m 0 $PY c7/fourier/code/p706_calib.py $m 2 _run/p706_m$m.json
  cmpl expected/c7/fourier/logs/p706_m$m.log _run/p706_m$m.out
  cmpj expected/c7/fourier/results/p706_m$m.json _run/p706_m$m.json
done
finish
