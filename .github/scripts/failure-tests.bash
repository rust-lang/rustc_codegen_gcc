#!/usr/bin/env bash

# A helper script for `build.steps.tests` in `failures.yml`.
#
# Expects these environment variables:
#   - `LIBGCCJIT_ENV_EXTRA`
#   - `LIBGCCJIT_EXTRA`
#   - `GITHUB_STEP_SUMMARY`
#
# This suite runs the tests known to fail, so only a build system error must
# fail the job.

# Without `set -o pipefail`, `tee` masks the exit status of `y.sh test`.
set -o pipefail

status=0

${LIBGCCJIT_ENV_EXTRA} ./y.sh test --release --clean --build-sysroot --test-failing-rustc ${LIBGCCJIT_EXTRA} 2>&1 | tee output_log || status=${?}
if [ "${status}" -ne 0 ] && [ "${status}" -ne 2 ]; then
    exit "${status}"
fi
rg --text "test result" output_log >>${GITHUB_STEP_SUMMARY}
