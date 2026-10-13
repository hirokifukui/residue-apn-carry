#!/bin/sh
# Representative re-run for Section repair (d0): power sums m=3,5,7,9; top coefficients (40/40/8 cases); correction rule (800 pairs);
# and pd6_cert.py: m=5 all 1024 local keys for h=a^3 (minima 27/26) plus the four m=5 reference tables.
. "$TOOLS/rep_lib.sh"
run h6_check 0 $PY c6/h/code/h6_check.py _run/h6_check.json
cmpl expected/c6/h/logs/h6_check.log _run/h6_check.out
cmpj expected/c6/h/results/h6_check.json _run/h6_check.json
run t303 0 $PY c1/code/t303_oracle.py c1/data          # regenerates c1/data/F_m5_r3.npy (natural table)
run pd6_cert 0 $PY c6/pd/code/pd6_cert.py _run/pd6_cert.json
cmpl expected/c6/pd/logs/pd6_cert.log _run/pd6_cert.out
cmpj expected/c6/pd/results/pd6_cert.json _run/pd6_cert.json
finish
