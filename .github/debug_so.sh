#!/usr/bin/env bash
# Automated diagnostic for the stack-overflow detection miscompilation.
# Runs in CI on failure; everything is printed to the job log.
set +e

SYSROOT="$PWD/build/build_sysroot/sysroot"
STDLIB="$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib"
export LD_LIBRARY_PATH="/usr/lib:$STDLIB"
ulimit -c unlimited 2>/dev/null

echo "===================== ENV ====================="
uname -a
ldd --version | head -1
echo "STDLIB=$STDLIB"
LIB=$(ls "$STDLIB"/libstd*.so 2>/dev/null | head -1)
echo "libstd.so: $LIB  size=$(stat -c%s "$LIB" 2>/dev/null)"

echo "===================== LOCATE BINARIES ====================="
OO=$(find build/rust -type f -path '*test/ui/runtime/out-of-stack/a' 2>/dev/null | head -1)
SP=$(find build/rust -type f -path '*test/ui/abi/stack-probes*/a' 2>/dev/null | head -1)
echo "out-of-stack binary: ${OO:-<none>}"
echo "stack-probes binary: ${SP:-<none>}"

debug_one() {
  local BIN="$1" ARG="$2"
  [ -z "$BIN" ] && return
  echo ""
  echo "############################################################"
  echo "# DEBUG  $BIN  $ARG"
  echo "############################################################"

  echo "----- reproduce (expect 139=SIGSEGV/undetected-bug, 134=SIGABRT/detected-ok) -----"
  "$BIN" "$ARG"; echo "exit=$?"

  echo "----- strace: clone + sigaltstack + SIGSEGV/BUS sigaction (per-thread) -----"
  # Hypothesis: the SPAWNED thread never completes make_handler, so it never
  # calls sigaltstack. In a working run each new thread issues sigaltstack.
  strace -f -e trace=clone,clone3,sigaltstack,rt_sigaction "$BIN" "$ARG" 2>strace.txt
  grep -nE "clone|sigaltstack|rt_sigaction\((SIGSEGV|SIGBUS)" strace.txt
  echo "sigaltstack total: $(grep -c 'sigaltstack(' strace.txt)   clone total: $(grep -cE 'clone[3]?\(' strace.txt)"

  echo "----- gdb: is make_handler / set_current_info reached by the SPAWNED thread? -----"
  gdb -q -batch -nx \
    -ex 'set pagination off' -ex 'set confirm off' \
    -ex 'rbreak stack_overflow.*imp.*make_handler' \
    -ex 'rbreak stack_overflow.*thread_info.*set_current_info' \
    -ex "run $ARG" \
    -ex 'printf "== HIT %s (thread %d) ==\n", "1", $_thread' -ex 'bt 4' -ex 'continue' \
    -ex 'printf "== HIT %s (thread %d) ==\n", "2", $_thread' -ex 'bt 4' -ex 'continue' \
    -ex 'printf "== HIT %s (thread %d) ==\n", "3", $_thread' -ex 'bt 4' -ex 'continue' \
    -ex 'printf "== HIT %s (thread %d) ==\n", "4", $_thread' -ex 'bt 4' -ex 'continue' \
    -ex 'printf "== HIT %s (thread %d) ==\n", "5", $_thread' -ex 'bt 4' -ex 'continue' \
    -ex 'printf "== reached program end / signal ==\n"' -ex 'info program' \
    --args "$BIN" "$ARG" 2>&1 \
    | grep -vE "Missing separate debuginfos|Download failed|Reading symbols|no debugging symbols" | head -160
}

debug_one "$OO" "silent-thread"
debug_one "$SP" "child-recurse"
debug_one "$SP" "child-frame"

echo ""
echo "===================== OBJDUMP make_handler (from failing libstd.so) ====================="
objdump -d "$LIB" 2>/dev/null | awk '
  /stack_overflow.*imp.*make_handler>:/{p=1}
  p{print}
  p&&/\tret/{exit}' | head -90

echo ""
echo "===================== NEED_ALTSTACK / set_current_info call sites ====================="
objdump -d "$LIB" 2>/dev/null | grep -nE "NEED_ALTSTACK|call.*make_handler|call.*Handler.*new|call.*set_current_info" | head -20

echo "===================== DEBUG DONE ====================="
