#!/bin/zsh
# C9 (P9-07) v2 (same driver, longer ORDER: + C3/C4/C6/C7 auxiliary files and their axiom files): build the Lean source closure module by module from SOURCES ONLY (no copied .olean),
# in a fresh directory, against the pinned Mathlib of $MATHLIB (lake env), one lean invocation per module,
# in import order. Stops at the first failure and propagates its exit code. Writes logs/<Name>.log and
# logs/<Name>.exit, logs/ENV.txt, logs/SOURCES_before.sha256 and logs/SOURCES_after.sha256.
# usage: build_closure.sh   (run from the closure root; overrides: CLOSURE_ROOT, CHECK_MATHLIB, CHECK_ELAN_BIN)
export PATH=${CHECK_ELAN_BIN:-$HOME/.elan/bin}:$PATH
ROOT=${CLOSURE_ROOT:-$PWD}
MATHLIB=${CHECK_MATHLIB:?set CHECK_MATHLIB to a Mathlib checkout at the pinned commit}
ORDER=(WarmStart SuffixReset ResetCompose CarryPD CarryZ CarryE_v2 OneRound Transport_v2 RepairCore_v2 W2Bridge ColsB_v3 ColsF_v2 TwoStep Bridge DigitSplit_v2 RepairLink_v2 VacuousZ4 MixAdd ThetaZ4_v3 AxiomsWarmStart AxiomsSuffixReset AxiomsResetCompose AxiomsCarryPD AxiomsC7 AxiomsC8 AxiomsC9_v2)
cd $ROOT || exit 92
mkdir -p logs build/ApnCipher
if [ -n "$(ls build/ApnCipher 2>/dev/null)" ]; then echo "build/ not empty: refuse (fresh build only)"; exit 93; fi
shasum -a 256 ApnCipher/*.lean ApnCipher.lean lakefile.toml lean-toolchain build_closure.sh > logs/SOURCES_before.sha256
{ echo "host: $(hostname)"; echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"; lean --version; echo "toolchain file: $(cat lean-toolchain)"; (cd $MATHLIB && echo "mathlib rev: $(git rev-parse HEAD 2>/dev/null)"; grep -A6 '"name": "mathlib"' lake-manifest.json | grep -E 'rev|inputRev' ); } > logs/ENV.txt 2>&1
cd $MATHLIB || exit 90
LP=$(lake env printenv LEAN_PATH) || exit 91
cd $ROOT
for n in $ORDER ApnCipher; do
  if [ $n = ApnCipher ]; then src=ApnCipher.lean; out=build/ApnCipher.olean; else src=ApnCipher/$n.lean; out=build/ApnCipher/$n.olean; fi
  LEAN_PATH=$LP:$ROOT/build lean --root=$ROOT -o $out $src > logs/$n.log 2>&1
  rc=$?; echo $rc > logs/$n.exit
  if [ $rc -ne 0 ]; then echo "FAIL $n $rc" > logs/RESULT.txt; exit $rc; fi
done
shasum -a 256 ApnCipher/*.lean ApnCipher.lean lakefile.toml lean-toolchain build_closure.sh > logs/SOURCES_after.sha256
cmp -s logs/SOURCES_before.sha256 logs/SOURCES_after.sha256 || { echo "FAIL sources changed" > logs/RESULT.txt; exit 94; }
grep -h "sorryAx\|declaration uses 'sorry'" logs/*.log && { echo "FAIL sorry" > logs/RESULT.txt; exit 95; }
echo "OK ${#ORDER} modules + root" > logs/RESULT.txt
exit 0
