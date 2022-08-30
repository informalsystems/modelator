#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

PREFIX="${1:-violation}"
TRACES_DIR="${2:-traces}"

TRACE_FILE=$(./trace_find.sh $PREFIX $TRACES_DIR)
echo "Trace file: $TRACE_FILE"

TRACE_LENGTH=$(./trace_length.sh $TRACE_FILE)
echo "Trace length: $TRACE_LENGTH"
