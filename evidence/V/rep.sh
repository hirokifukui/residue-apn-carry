#!/bin/sh
# Representative re-run for Theorem V (decomposition = literal evaluation of all 16^6 theta, toy m=2, w=2): 3 of the 32 cases.
. "$TOOLS/rep_lib.sh"
D=c5/attack
run selftest_v2 0 $PY $D/code/atk_selftest_v2.py _run/selftest_v2.json
cmpl expected/$D/logs/selftest_v2.log _run/selftest_v2.out
run literal 0 $PY $D/code/atk_runs_v2.py literal _run/p503_literal_sub.json F_toy_m2 2 2 4 E:0,RF:0,RP:0
cmpsel expected/$D/logs/p503_literal_m2w2.log _run/literal.out "'oracle': 'E:0'" "'oracle': 'RF:0'" "'oracle': 'RP:0'"
finish
