#!/bin/sh
# Representative re-run for Theorem UE (energy identity, calE_Z, calE_B; m = 5 all 11 tables, m = 7 all 8 tables).
. "$TOOLS/rep_lib.sh"
home_link || finish
run t303 0 $PY c1/code/t303_oracle.py c1/data
run t311a 0 $PY c1/code/t311a_rowmax.py c1/data _run/t311a_rowmax.json
mkdir -p c3/a1/data c3/a1/results c5/a1/results
run a1_lifts 0 $PY c3/a1/code/a1_lifts.py
cmpl expected/c3/a1/logs/a1_lifts.log _run/a1_lifts.out
run a1_gpair 0 $PY c3/a1/code/a1_gpair.py 5
cmpl expected/c3/a1/logs/a1_gpair_m5.log _run/a1_gpair.out
run ue_m5 0 $PY c5/a1/code/a1c5_ue.py 5
cmpl expected/c5/a1/logs/a1c5_ue_m5.log _run/ue_m5.out
cmpj expected/c5/a1/results/a1c5_ue_m5.json c5/a1/results/a1c5_ue_m5.json
run ue_m7 0 $PY c5/a1/code/a1c5_ue.py 7
cmpl expected/c5/a1/logs/a1c5_ue_m7.log _run/ue_m7.out
cmpj expected/c5/a1/results/a1c5_ue_m7.json c5/a1/results/a1c5_ue_m7.json
finish
