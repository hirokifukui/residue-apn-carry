#!/bin/sh
# Self-test of the comparison helper (added in version 1.0.1): cmp_json.py must reject NaN/Infinity and real differences.
. "$TOOLS/rep_lib.sh"
run test_cmp_json 0 $PY "$TOOLS/test_cmp_json.py"
finish
