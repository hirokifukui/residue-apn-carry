#!/bin/sh
# Representative re-run for Theorem W2 (exact N*EDP_2 values, m = 5).
. "$TOOLS/rep_lib.sh"
run t303 0 $PY c1/code/t303_oracle.py c1/data
cmpl expected/c1/logs/run_all/t303.log _run/t303.out
run p210 0 $PY c2/cost/p210_hermite_cost.py c2/cost
cmpl expected/c2/cost/p210.log _run/p210.out
run p312 0 $PY c3/pd/p312_pd_roles.py c3/pd
cmpl expected/c3/pd/p312.log _run/p312.out
cmpj expected/c3/pd/p312_results.json c3/pd/p312_results.json
# p301 (natural 185/128, h=0 311/128, adversarial 31/16, random 303/256) imports sympy at top level.
if have_sympy; then
  home_link
  run t311a 0 $PY c1/code/t311a_rowmax.py c1/data _run/t311a_rowmax.json
  mkdir -p c3/a1/data c3/a1/results
  run a1_lifts 0 $PY c3/a1/code/a1_lifts.py
  run a1_gpair 0 $PY c3/a1/code/a1_gpair.py 5
  run p301 0 $PY c3/code/p301_warmstart.py . _run/p301_warmstart.json
  cmpl expected/c3/logs/p301.log _run/p301.out
  cmpj expected/c3/results/p301_warmstart.json _run/p301_warmstart.json finite
else
  echo "  NOT_RUN p301_warmstart.py: sympy is not installed (recorded output: expected/c3/logs/p301.log, exit 0)"
fi
finish
