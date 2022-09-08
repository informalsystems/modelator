#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

[ $# -eq 0 ] && echo "Usage: $0 <TRACES_DIR>" && exit 1


TRACES_DIR="$1"

DIR=$TRACES_DIR
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1


# last file in the directory by time
LAST_FILE=$(ls -rt $DIR | grep .itf.json | tail -1)

# Return last generated trace file
echo $DIR/$LAST_FILE
