#!/bin/sh
# Representative re-run for Theorem G / Proposition Minv: both implementations (code/ = author, audit_code/ = audit).
. "$TOOLS/rep_lib.sh"
C=c8/r1/code; A=c8/r1/audit_code; R=expected/c8/r1/results; AR=expected/c8/r1/audit_results
run t1_verify 0 $PY $C/t1_verify.py $C _run/t1_verify.json
cmpl $R/t1_verify.log _run/t1_verify.out
cmpj $R/t1_verify.json _run/t1_verify.json
run t2_m3 0 $PY $C/t2_analyze.py $C _run/t2_m3.json 3
cmpl $R/t2_m3.log _run/t2_m3.out
cmpj $R/t2_m3.json _run/t2_m3.json
run t3_msurvey 0 $PY $C/t3_extra.py $C _run msurvey
cmpl $R/t3_msurvey.log _run/t3_msurvey.out
cmpj $R/t3_msurvey.json _run/t3_msurvey.json
run a_main_m3 0 $PY $A/a_main.py _run/a_main_m3.json 3
cmpl $AR/a_main_m3.log _run/a_main_m3.out
cmpj $AR/a_main_m3.json _run/a_main_m3.json
run a_msurvey 0 $PY $A/a_msurvey.py _run/a_msurvey.json
cmpl $AR/a_msurvey.log _run/a_msurvey.out
cmpj $AR/a_msurvey.json _run/a_msurvey.json
# Standard check (version 1.0.1): re-verify the 40 RECORDED adversarial witnesses (p, K, eps, h) without re-running the search.
run witnesses_m3 0 $PY check_recorded_witnesses.py $AR/a_adv_m3.json _run/witnesses_m3.json
# Optional: re-run the hill-climbing search itself (G_MINV_SEARCH=1). The search accepts floating-point ties (v >= cur), so on
# other NumPy versions it may end at different witnesses h; its result is then reported, not compared field by field.
if [ "${G_MINV_SEARCH:-0}" = 1 ]; then
  run a_adv_m3_search 0 $PY $A/a_adv.py _run/a_adv_m3.json m3 11 40
  cmpsel $AR/a_adv_m3.log _run/a_adv_m3_search.out "max ratio"
  echo "  NOTE search re-run: witnesses h are reported in _run/a_adv_m3.json and not compared (see README)"
fi
finish
