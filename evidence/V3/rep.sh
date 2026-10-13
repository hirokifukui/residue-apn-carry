#!/bin/sh
# Representative re-run for Theorem V(3): RP law = RF | D for M=5, Q=3 (all 120 permutations), plus the exact bounds.
. "$TOOLS/rep_lib.sh"
run c5_selftest_v2 0 $PY c5/attack/code/atk_selftest_v2.py _run/selftest_v2.json
cmpl expected/c5/attack/logs/selftest_v2.log _run/c5_selftest_v2.out
run p607 0 $PY c6/attack/code/p607_rp_cond_v2.py _run/p607_rp_cond_v2.json
cmpl expected/c6/attack/logs/p607_rp_cond_v2.log _run/p607.out
cmpj expected/c6/attack/results/p607_rp_cond_v2.json _run/p607_rp_cond_v2.json tiny cases extra structural P607
finish
