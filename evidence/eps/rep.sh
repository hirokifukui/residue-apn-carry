#!/bin/sh
# Representative re-run for Theorem eps (one-round bound Delta(B) = q).  Run via run_all_representatives.sh.
. "$TOOLS/rep_lib.sh"
run t303 0 $PY c1/code/t303_oracle.py c1/data
cmpl expected/c1/logs/run_all/t303.log _run/t303.out
cmpj expected/c1/data/t303_oracle.json c1/data/t303_oracle.json
run t311a 0 $PY c1/code/t311a_rowmax.py c1/data _run/t311a_rowmax.json
cmpl expected/c1/logs/run_all/t311a.log _run/t311a.out
cmpj expected/c1/results/t311a_rowmax.json _run/t311a_rowmax.json
run p202_m5 0 $PY c2/code/p202_epsilon.py c1/data _run/p202_epsilon_m5.json 5 F_m5_r3 F_m5_r3_adversarialG
cmpl expected/c2/logs/p202_m5.log _run/p202_m5.out
cmpj expected/c2/results/p202_epsilon_m5.json _run/p202_epsilon_m5.json
run p202b 0 $PY c2/code/p202b_general_rho.py c1/data _run/p202b_general_rho.json
cmpl expected/c2/logs/p202b.log _run/p202b.out
cmpj expected/c2/results/p202b_general_rho.json _run/p202b_general_rho.json
finish
