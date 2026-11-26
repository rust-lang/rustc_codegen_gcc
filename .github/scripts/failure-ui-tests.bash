#!/usr/bin/env bash

# A helper script for `build.steps.ui-tests` in `failures.yml`.
#
# Expects these environment variables:
#   - `LIBGCCJIT_ENV_EXTRA`
#   - `LIBGCCJIT_EXTRA`
#
# This suite runs tests that fail, so only a build system error must fail the
# job here.

# Without `set -o pipefail`, `tee` masks the exit status of `y.sh test`.
set -o pipefail

status=0

${LIBGCCJIT_ENV_EXTRA} ./y.sh test --release --test-failing-ui-pattern-tests ${LIBGCCJIT_EXTRA} 2>&1 | tee output_log_ui || status=${?}
if [ "${status}" -ne 0 ] && [ "${status}" -ne 2 ]; then
    exit "${status}"
fi
if grep -q "the compiler unexpectedly panicked" output_log_ui; then
    echo "Error: 'the compiler unexpectedly panicked' found in output logs. CI Error!!"
    exit 1
fi
