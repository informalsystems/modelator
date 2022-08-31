#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

[ $# -eq 0 ] && echo "Usage: $0 <TRACE_FILE> [<TRACES_DIR>]" && exit 1

TRACE_FILE="$1"

[ ! -f "$TRACE_FILE" ] && echo -e "ERROR: file $TRACE_FILE does not exists" && exit 1

TRACE_LENGTH=$(cat $TRACE_FILE | jq '.states[]."#meta".index' | tail -1)
echo $TRACE_LENGTH
