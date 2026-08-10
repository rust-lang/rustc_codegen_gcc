/* Strong definitions for tests/run/bug_linkage_weak.rs.
 *
 * `provider` is a STRONG definition: it must override the `#[linkage = "weak"]` Rust
 * definition of the same symbol. cg_gcc currently emits the Rust one as GLOBAL instead of
 * WEAK, which makes the link fail with a duplicate-symbol error. `call_provider` gives the
 * Rust side something GCC-compiled to call so the resolution happens in an object cg_gcc
 * did not produce. */
#include <stdint.h>

uint32_t provider(void) {
    return 999;
}

uint32_t call_provider(void) {
    return provider();
}
