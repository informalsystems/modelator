#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

[ $# -eq 0 ] && echo "Usage: $0 <PROPERTY_NAME> [<TRACES_DIR>]" && exit 1

PROPERTY_NAME="$1"
TRACES_DIR="${2:-traces}"

DIR="$TRACES_DIR"
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1

TIMESTAMP_SUBDIR=$(ls -rt $TRACES_DIR | tail -1)
DIR="$DIR/$TIMESTAMP_SUBDIR/$PROPERTY_NAME"
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1

# Return the number of files in the directory
# - tail -n+2 for discarding the first file (violation.itf.json)
# - xargs for trimming whitespace
NUM_TRACE_FILES=$(ls -rt $DIR | grep .itf.json | tail -n+1 | wc -l | xargs)
echo $NUM_TRACE_FILES
