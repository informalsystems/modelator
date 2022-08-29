#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

TRACES_DIR="${1:-traces}"

TIMESTAMP_SUBDIR=$(ls -rt $TRACES_DIR | tail -1)
DIR=$TRACES_DIR/$TIMESTAMP_SUBDIR

# Return the number of files in the directory
# - tail -n+2 for discarding the first file (violation.itf.json)
# - xargs for trimming whitespace
TRACE_FILES=$(ls -rt $DIR | tail -n+2 | wc -l | xargs)
echo $TRACE_FILES
