# rep_lib.sh -- helpers sourced by evidence/<row>/rep.sh (POSIX sh).
# Required environment: TOOLS = directory of this file; cwd = a writable temporary COPY of evidence/<row>/.
# Results of re-runs go to ./_run/.  The variable FAIL becomes 1 on any unexpected exit or mismatch.
PY="python3 -I -B"
FAIL=0
mkdir -p _run

# run NAME EXPECTED_EXIT CMD...   (stdout -> _run/NAME.out, stderr -> _run/NAME.err)
run() {
  _n=$1; _want=$2; shift 2
  _t0=$(date +%s)
  "$@" > "_run/$_n.out" 2> "_run/$_n.err"
  _rc=$?
  _t1=$(date +%s)
  echo "  RUN $_n exit=$_rc (expected $_want) wall=$((_t1 - _t0))s"
  if [ "$_rc" -ne "$_want" ]; then
    FAIL=1; tail -n 5 "_run/$_n.err" | sed 's/^/    stderr: /'
  fi
}

# cmpl RECORDED_LOG ACTUAL_STDOUT : every line of the recorded log (minus harness lines EXIT=/exit=)
# must appear in the re-run's stdout (cmp_lines.py rules).
cmpl() {
  _e="_run/expected_lines.$$.txt"
  grep -v -e '^EXIT=' -e '^exit=' "$1" > "$_e"
  if $PY "$TOOLS/cmp_lines.py" "$_e" "$2" > "_run/cmp.$$.txt" 2>&1; then
    echo "  CMP OK  $1 :: $(tail -n 1 "_run/cmp.$$.txt")"
  else
    FAIL=1; echo "  CMP BAD $1"; sed 's/^/    /' "_run/cmp.$$.txt" | tail -n 8
  fi
}

# cmpsel RECORDED_LOG ACTUAL_STDOUT PATTERN... : only recorded lines matching one of the fixed-string patterns.
cmpsel() {
  _log=$1; _act=$2; shift 2
  _e="_run/expected_sel.$$.txt"; : > "$_e"
  for _p in "$@"; do grep -F -e "$_p" "$_log" >> "$_e"; done
  if $PY "$TOOLS/cmp_lines.py" "$_e" "$_act" > "_run/cmp.$$.txt" 2>&1; then
    echo "  CMP OK  $_log (selected) :: $(tail -n 1 "_run/cmp.$$.txt")"
  else
    FAIL=1; echo "  CMP BAD $_log (selected)"; sed 's/^/    /' "_run/cmp.$$.txt" | tail -n 8
  fi
}

# cmpj RECORDED_JSON ACTUAL_JSON [TOPLEVEL_KEY ...]
cmpj() {
  if $PY "$TOOLS/cmp_json.py" "$@" > "_run/cmpj.$$.txt" 2>&1; then
    echo "  CMPJSON OK  $1 :: $(tail -n 1 "_run/cmpj.$$.txt")"
  else
    FAIL=1; echo "  CMPJSON BAD $1"; sed 's/^/    /' "_run/cmpj.$$.txt" | tail -n 8
  fi
}

# home_link : some historical scripts hard-code ~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher.
# Without editing them, point that path (inside the TEMPORARY empty HOME made by the runner) at this copy.
home_link() {
  if [ "${EVIDENCE_TEMP_HOME:-0}" != 1 ]; then
    echo "  refusing to create links in a non-temporary HOME (set EVIDENCE_TEMP_HOME=1 only for a throwaway HOME)"; FAIL=1; return 1
  fi
  mkdir -p "$HOME/Library/CloudStorage/Dropbox/Scripts/Champagne" &&
  ln -s "$(pwd)" "$HOME/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher"
}

have_sympy() { python3 -I -c 'import sympy' > /dev/null 2>&1; }

finish() {
  if [ "$FAIL" -eq 0 ]; then echo "  ROW RESULT: OK"; else echo "  ROW RESULT: FAIL"; fi
  exit "$FAIL"
}
