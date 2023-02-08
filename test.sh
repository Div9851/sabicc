#!/bin/bash
executable=./target/debug/sabicc

assert() {
    expected="$1"
    input="$2"

    $executable "$input" > tmp.s || exit
    gcc -static -o tmp tmp.s
    ./tmp
    actual="$?"

    if [ "$actual" = "$expected" ]; then
        echo "$input => $actual"
    else
        echo "$input => $expected expected, but got $actual"
        exit 1
    fi  
}

cargo build

assert 0 0
assert 42 42

echo OK
