#!/bin/bash
tmp=`mktemp -d /tmp/sabicc-test-XXXXXX`
trap 'rm -rf $tmp' INT TERM HUP EXIT
echo > $tmp/empty.c

check() {
    if [ $? -eq 0 ]; then
        echo "testing $1 ... passed"
    else
        echo "testing $1 ... failed"
        exit 1
    fi
}

# -o
rm -f $tmp/out
cargo run -- -o $tmp/out $tmp/empty.c
[ -f $tmp/out ]
check -o

# --help
cargo run -- --help 2>&1 | grep -q sabicc
check --help

echo OK
