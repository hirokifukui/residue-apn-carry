#!/bin/sh
# Cost row 4 (one F, PD table h=a^3: 75 AND, 98 XOR, 1 NOT).  pd5_circuit_v2.main() needs an unpublished external
# auditor table for an optional cross-check, so the unedited module is driven by the new wrapper run_author_only.py,
# which compares with the author tables only and with the recorded counts / hashes.
. "$TOOLS/rep_lib.sh"
run author_only 0 $PY run_author_only.py expected/c5/pd/results/pd5_circuit_v2.json _run
grep -F 'm5_hX3 {"AND": 75, "XOR": 98, "NOT": 1' _run/author_only.out > /dev/null || { echo "  m5_hX3 count line missing"; FAIL=1; }
finish
