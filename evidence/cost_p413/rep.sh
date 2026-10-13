#!/bin/sh
# Cost rows 1-3 (Feistel 75, S2 natural 145, S2 PD 235 AND): p413_cost.py imports sympy at top level.
. "$TOOLS/rep_lib.sh"
if have_sympy; then
  run p413 0 $PY c4/cost/p413_cost.py c2/cost/p210_results.json c4/spec/CANDIDATE_P4_SPLIT_TAIL.json c3/spec/CANDIDATE_P3B_THREE.json _run/p413_results.json
  cmpl expected/c4/cost/p413.log _run/p413.out
else
  echo "  NOT_RUN p413_cost.py: sympy is not installed (recorded output: expected/c4/cost/p413.log, exit 0)"
fi
finish
