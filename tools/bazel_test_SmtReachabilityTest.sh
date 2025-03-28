#!/bin/bash

set -euo pipefail

BAZEL="bazelisk"

if ! type "${BAZEL}" &> /dev/null; then
  echo "This script works better with bazelisk. Use 'go get github.com/bazelbuild/bazelisk' to get it.'"
  echo
  BAZEL="bazel"
fi

if [ "${1-}" = "-d" ]
then
  DEBUG="--jvm_flag=-agentlib:jdwp=transport=dt_socket,server=y,suspend=n,address=5009 --jvm_flag=-ea"
else
  DEBUG=
fi

# test `SmtReachabilityTest`
TARGET="//projects/allinone:smt_tests"
FLAGS="--test_filter=org.batfish.minesweeper.smt.SmtReachabilityTest#"
${BAZEL} build ${TARGET}
${BAZEL} test ${TARGET} ${FLAGS}
