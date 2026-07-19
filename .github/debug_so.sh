#!/usr/bin/env bash
# Automated diagnostic for the stack-overflow detection miscompilation.
# Runs in CI on failure; everything is printed to the job log.
set +e

SYSROOT="$PWD/build/build_sysroot/sysroot"
STDLIB="$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib"
BACKEND="$PWD/target/release/librustc_codegen_gcc.so"
RUSTC="$(rustup which rustc 2>/dev/null || echo rustc)"
export LD_LIBRARY_PATH="/usr/lib:$STDLIB"
ulimit -c unlimited 2>/dev/null

echo "===================== ENV ====================="
uname -a
ldd --version 2>/dev/null | head -1
LIB=$(ls "$STDLIB"/libstd*.so 2>/dev/null | head -1)
echo "libstd.so: $LIB  size=$(stat -c%s "$LIB" 2>/dev/null)"

# $1 = binary path, $2 = arg (the subprocess mode that overflows)
debug_bin() {
  local BIN="$1" ARG="$2"
  [ -z "$BIN" ] || [ ! -x "$BIN" ] && { echo "SKIP (no binary): $BIN"; return; }
  echo ""
  echo "############################################################"
  echo "# DEBUG  $BIN  $ARG"
  echo "############################################################"

  echo "----- reproduce (139=SIGSEGV/undetected-BUG, 134=SIGABRT/detected-ok) -----"
  "$BIN" "$ARG"; echo "exit=$?"

  echo "----- strace: clone + sigaltstack per thread (does the SPAWNED thread set up its altstack?) -----"
  strace -f -e trace=clone,clone3,sigaltstack,rt_sigaction "$BIN" "$ARG" 2>/tmp/strace.txt
  grep -nE "clone|sigaltstack|rt_sigaction\((SIGSEGV|SIGBUS)" /tmp/strace.txt
  echo "sigaltstack total: $(grep -c 'sigaltstack(' /tmp/strace.txt)   clone total: $(grep -cE 'clone[3]?\(' /tmp/strace.txt)"

  echo "----- gdb: is make_handler / set_current_info reached by the SPAWNED thread? -----"
  gdb -q -batch -nx \
    -ex 'set pagination off' -ex 'set confirm off' \
    -ex 'rbreak stack_overflow.*imp.*make_handler' \
    -ex 'rbreak stack_overflow.*thread_info.*set_current_info' \
    -ex "run $ARG" \
    -ex 'printf "== HIT#1 thread=%d ==\n", $_thread' -ex 'bt 3' -ex 'continue' \
    -ex 'printf "== HIT#2 thread=%d ==\n", $_thread' -ex 'bt 3' -ex 'continue' \
    -ex 'printf "== HIT#3 thread=%d ==\n", $_thread' -ex 'bt 3' -ex 'continue' \
    -ex 'printf "== HIT#4 thread=%d ==\n", $_thread' -ex 'bt 3' -ex 'continue' \
    -ex 'printf "== HIT#5 thread=%d ==\n", $_thread' -ex 'bt 3' -ex 'continue' \
    -ex 'printf "== end ==\n"' -ex 'info program' \
    --args "$BIN" "$ARG" 2>&1 \
    | grep -vE "Missing separate|Download failed|Reading symbols|warning: File" | head -140
}

echo "===================== REAL COMPILETEST BINARIES ====================="
OO=$(find build/rust -type f -path '*out-of-stack/a' 2>/dev/null | head -1)
SP=$(find build/rust -type f -path '*stack-probes*/a' 2>/dev/null | head -1)
echo "out-of-stack: ${OO:-<none>}"
echo "stack-probes: ${SP:-<none>}"
debug_bin "$OO" "silent-thread"
debug_bin "$SP" "child-recurse"
debug_bin "$SP" "child-frame"

echo ""
echo "===================== COMPARISON: freshly-built minimal repro ====================="
D=$(mktemp -d)
cat > "$D/repro.rs" <<'RS'
use std::hint::black_box;
use std::thread::Builder;
fn silent() { let b = [0u8; 1000]; black_box(b); silent(); }
fn main() { Builder::new().name("ferris".into()).spawn(silent).unwrap().join().ok(); }
RS
"$RUSTC" -Zcodegen-backend="$BACKEND" --sysroot "$SYSROOT" -Cprefer-dynamic -o "$D/a" "$D/repro.rs" 2>/dev/null
debug_bin "$D/a" ""

echo ""
echo "===================== OBJDUMP make_handler ====================="
objdump -d "$LIB" 2>/dev/null | awk '
  /stack_overflow.*imp.*make_handler>:/{p=1}
  p{print}
  p&&/\tret/{exit}' | head -90

echo "===================== DEBUG DONE ====================="
