#!/bin/sh
# Representative re-run for Theorem R1 (block norms; m = 3, 5: 16 of the 20 tables; m = 7 is REUSED_RECORD).
. "$TOOLS/rep_lib.sh"
for m in 3 5; do
  run p707_m$m 0 $PY c7/fourier/code/p707_gram.py $m 2 _run/p707_m$m.json
  cmpl expected/c7/fourier/logs/p707_m$m.log _run/p707_m$m.out
  cmpj expected/c7/fourier/results/p707_m$m.json _run/p707_m$m.json
done
run p706_m3 0 $PY c7/fourier/code/p706_calib.py 3 2 _run/p706_m3.json
cmpl expected/c7/fourier/logs/p706_m3.log _run/p706_m3.out
echo "  REUSED_RECORD p707_gram.py 7 0 (4 tables, about 4 min here; iterative operator norms)"
finish
