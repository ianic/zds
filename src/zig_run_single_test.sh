#!/bin/bash

if [[ -z "$2" ]]; then
    zig test $1 2>&1 | cat
else
    filter=$(sed -n 1,$2p $1 | sed -n 's/^test.*"\(.*\)".*{$/\1/p' | tail -1)
    [[ -z "$filter" ]] && {
        echo "No test find before line $2"
        exit 1
    }
    # echo "Running test '$filter'"
    zig test --test-filter "$filter" $1 2>&1 | cat
fi
