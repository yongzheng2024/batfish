#!/bin/bash
set -e  # stop the script on any error (a command exits with a non-zero status)

# For Mac
if [ "Darwin" = $(uname -s) ]; then
    if ! [ -x "$(command -v greadlink)"  ]; then
        brew install coreutils
    fi
    BIN_PATH=$(greadlink -f "$0")
    ROOT_DIR=$(dirname $(dirname "$BIN_PATH"))
# For Linux
else
    BIN_PATH=$(readlink -f "$0")
    ROOT_DIR=$(dirname $(dirname "$BIN_PATH"))
fi

BAZEL="bazelisk"

TARGET_EXPRESSION="//projects/allinone:smt_tests"
BAZEL_COMMAND="test"
BAZEL_FLAGS=(
    "--test_filter=org.batfish.minesweeper.smt.SmtReachabilityTest#"
    "--cache_test_results=no"
)
${BAZEL} ${BAZEL_COMMAND} ${TARGET_EXPRESSION} ${BAZEL_FLAGS}
