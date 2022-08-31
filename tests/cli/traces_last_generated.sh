#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

[ $# -eq 0 ] && echo "Usage: $0 <PROPERTY_NAME> [<TRACES_DIR>]" && exit 1

PROPERTY_NAME="$1"
TRACES_DIR="${2:-traces}"

DIR=$TRACES_DIR
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1

TIMESTAMP_SUBDIR=$(ls -rt $TRACES_DIR | tail -1)
DIR=$DIR/$TIMESTAMP_SUBDIR
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1

DIR=$DIR/$PROPERTY_NAME
[ ! -d "$DIR" ] && echo "Directory $DIR does not exist" && exit 1

# last file in the directory by time
LAST_FILE=$(ls -rt $DIR | tail -1)

# Return last generated trace file
echo $DIR/$LAST_FILE
