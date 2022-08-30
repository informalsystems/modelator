#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

TRACE_FILE="$1"

[ -z $TRACE_FILE ] && echo -e "ERROR: invalid arguments\nUsage: $0 <TRACE_FILE>" && exit 1

[ ! -f $TRACE_FILE ] && echo -e "ERROR: file $TRACE_FILE does not exists" && exit 1

TRACE_LENGTH=$(cat $TRACE_FILE | jq '.states[]."#meta".index' | tail -1)
echo $TRACE_LENGTH
