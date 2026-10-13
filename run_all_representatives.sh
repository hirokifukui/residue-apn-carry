#!/bin/sh
# run_all_representatives.sh -- re-run one representative command per finite-check row of Section 7 and compare
# with the recorded / expected outputs.  POSIX sh.  Run from the repository root:
#     sh run_all_representatives.sh            (all rows)
#     sh run_all_representatives.sh eps UE     (selected rows; 'public' = the three checks/ scripts)
# Each row runs in a fresh temporary directory (a copy of evidence/<row>/) with HOME set to a fresh empty
# directory and python3 -I -B.  Nothing outside the temporary directories is written.
# Exit status: 0 iff every executed command had its expected exit code and every comparison agreed.
# Rows marked NOT_RUN inside their rep.sh (missing optional dependency or inputs) do not count as failures;
# they are listed in the summary.  Total wall time on a 2-core machine: about 8-10 minutes.
set -u
ROOT=$(pwd)
if [ ! -d "$ROOT/evidence" ] || [ ! -d "$ROOT/checks" ]; then
  echo "run from the repository root (needs evidence/ and checks/)"; exit 2
fi
command -v python3 > /dev/null 2>&1 || { echo "python3 not found"; exit 2; }
python3 -I -c 'import numpy' 2> /dev/null || { echo "numpy not importable by python3 -I"; exit 2; }

ROWS="public eps W2 UE repair_d0 general_d pf R1 G_Minv V V3 theta cost_p413 cost_F_ha3"
[ $# -gt 0 ] && ROWS="$*"
TOP=$(mktemp -d "${TMPDIR:-/tmp}/evrep.XXXXXX") || exit 2
SUMMARY="$TOP/SUMMARY.txt"; : > "$SUMMARY"
ALLFAIL=0

public_checks() {
  # the three public checkers, from the repository root, outputs into a temp dir, compared with checks/expected/
  O="$1"; H="$2"; F=0
  for spec in "p802_zexact.py:p802_zexact:0:" "p803_steps_v2.py:p803_steps_v2:0:" \
              "p803_steps_v2.py:p803_fault:1:--fault-C1" "p805_p806.py:p805_p806:0:"; do
    s=$(echo "$spec" | cut -d: -f1); n=$(echo "$spec" | cut -d: -f2)
    want=$(echo "$spec" | cut -d: -f3); extra=$(echo "$spec" | cut -d: -f4)
    # shellcheck disable=SC2086
    HOME="$H" python3 -I -B "checks/$s" "$O/$n.json" $extra > "$O/$n.out" 2> "$O/$n.err"; rc=$?
    echo "  RUN checks/$s $extra exit=$rc (expected $want)"
    [ "$rc" -eq "$want" ] || F=1
    if [ "$want" -eq 0 ]; then
      if HOME="$H" python3 -I -B evidence/_tools/cmp_json.py "checks/expected/$n.json" "$O/$n.json" > "$O/$n.cmp" 2>&1; then
        echo "  CMPJSON OK  checks/expected/$n.json :: $(tail -n 1 "$O/$n.cmp")"
      else
        F=1; echo "  CMPJSON BAD checks/expected/$n.json"; tail -n 5 "$O/$n.cmp" | sed 's/^/    /'
      fi
    fi
  done
  [ "$F" -eq 0 ] && echo "  ROW RESULT: OK" || echo "  ROW RESULT: FAIL"
  return "$F"
}

for row in $ROWS; do
  echo "== $row"
  T="$TOP/$row"; mkdir -p "$T/home" "$T/out"
  t0=$(date +%s)
  if [ "$row" = public ]; then
    public_checks "$T/out" "$T/home" > "$T/log.txt" 2>&1; rc=$?
  elif [ -f "evidence/$row/rep.sh" ]; then
    cp -R "evidence/$row" "$T/w" && cp -R evidence/_tools "$T/_tools" || { echo "copy failed"; ALLFAIL=1; continue; }
    ( cd "$T/w" && HOME="$T/home" EVIDENCE_TEMP_HOME=1 TOOLS="$T/_tools" sh ./rep.sh ) > "$T/log.txt" 2>&1; rc=$?
  else
    echo "  unknown row $row" > "$T/log.txt"; rc=2
  fi
  t1=$(date +%s)
  cat "$T/log.txt"
  nr=$(grep -c 'NOT_RUN\|REUSED_RECORD' "$T/log.txt")
  echo "$row exit=$rc wall=$((t1 - t0))s not_run_or_reused_notes=$nr" >> "$SUMMARY"
  [ "$rc" -eq 0 ] || ALLFAIL=1
done
echo "== SUMMARY (temp dir $TOP)"
cat "$SUMMARY"
echo "RUN_ALL_STATUS=$ALLFAIL"
exit "$ALLFAIL"
