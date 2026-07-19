#!/usr/bin/env bash
# Automated diagnostic for the stack-overflow detection miscompilation.
# Runs in CI on failure; everything is printed to the job log.
# Compiletest deletes the run-pass exe, so we compile our own repro (which
# matches the failing tests) and trace it.
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
echo "backend:   $BACKEND"
echo "rustc:     $RUSTC"

echo "===================== BUILD REPRO ====================="
D=$(mktemp -d)
cat > "$D/repro.rs" <<'RS'
use std::hint::black_box;
use std::mem::MaybeUninit;
use std::thread;
use std::env;
#[allow(unconditional_recursion)]
fn recurse(a: &MaybeUninit<[u64; 1024]>) {
    black_box(a.as_ptr() as u64);
    let l: MaybeUninit<[u64; 1024]> = MaybeUninit::uninit();
    recurse(&l);
}
fn overflow_recurse() { recurse(&MaybeUninit::uninit()); }
fn overflow_frame() {
    const S: usize = 512 * 1024;
    thread::Builder::new().stack_size(S).spawn(|| {
        let l: MaybeUninit<[u8; 2 * S]> = MaybeUninit::uninit();
        black_box(l.as_ptr() as u64);
    }).unwrap().join().unwrap();
}
fn silent() { let b = [0u8; 1000]; black_box(b); silent(); }
fn main() {
    match env::args().nth(1).as_deref() {
        Some("child-recurse") => { thread::spawn(overflow_recurse).join().unwrap(); }
        Some("child-frame")   => overflow_frame(),
        Some("silent-thread") => { thread::Builder::new().name("ferris".into())
                                       .spawn(silent).unwrap().join().ok(); }
        _ => panic!("need arg"),
    }
}
RS
"$RUSTC" -Zcodegen-backend="$BACKEND" --sysroot "$SYSROOT" -Cprefer-dynamic -g -o "$D/a" "$D/repro.rs"
echo "compiled repro: $(ls -l "$D/a" 2>/dev/null)"

debug_one() {
  local ARG="$1"
  echo ""
  echo "############################################################"
  echo "# DEBUG  repro  $ARG"
  echo "############################################################"

  echo "----- reproduce (139=SIGSEGV/undetected-BUG, 134=SIGABRT/detected-ok) -----"
  "$D/a" "$ARG"; echo "exit=$?"

  echo "----- strace: clone + sigaltstack per thread (does the SPAWNED thread set up its altstack?) -----"
  strace -f -e trace=clone,clone3,sigaltstack,rt_sigaction "$D/a" "$ARG" 2>"$D/strace.txt"
  grep -nE "clone|sigaltstack|rt_sigaction\((SIGSEGV|SIGBUS)" "$D/strace.txt"
  echo "sigaltstack total: $(grep -c 'sigaltstack(' "$D/strace.txt")   clone total: $(grep -cE 'clone[3]?\(' "$D/strace.txt")"

  echo "----- gdb: is make_handler / set_current_info reached by the SPAWNED thread? + NEED_ALTSTACK -----"
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
    --args "$D/a" "$ARG" 2>&1 \
    | grep -vE "Missing separate|Download failed|Reading symbols|warning: File" | head -150
}

debug_one "silent-thread"
debug_one "child-recurse"
debug_one "child-frame"

echo ""
echo "===================== OBJDUMP make_handler ====================="
objdump -d "$LIB" 2>/dev/null | awk '
  /stack_overflow.*imp.*make_handler>:/{p=1}
  p{print}
  p&&/\tret/{exit}' | head -90

echo "===================== DEBUG DONE ====================="
