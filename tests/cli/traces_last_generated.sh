#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

TRACES_DIR="${1:-traces}"

TIMESTAMP_SUBDIR=$(ls -rt $TRACES_DIR | tail -1)

# last file in the directory by time
LAST_FILE=$(ls -rt $TRACES_DIR/$TIMESTAMP_SUBDIR | tail -1)

echo $TRACES_DIR/$TIMESTAMP_SUBDIR/$LAST_FILE
