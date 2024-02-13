#!/bin/sh 

# Change the -I and -L paths to point to your Z3 install and build:
swipl-ld -I/Users/uribe/git/z3/src/api/ -L/Users/uribe/git/z3/build/ -o z3_swi_foreign -shared z3_swi_foreign.c -lz3

