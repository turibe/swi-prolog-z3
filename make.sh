#!/bin/sh 

# You should have a symbolic link to, or copy of, libz3.dylib in this directory.

# Change the -I path to point to your Z3 install and build:

swipl-ld -O1 -I/Users/uribe/git/z3/src/api/ -I/opt/homebrew/Cellar/gmp/6.3.0/include/ -L. -o z3_swi_foreign -shared z3_swi_foreign.c -lz3 -lgmp

# swipl-ld -O3 -Wall -I/Users/uribe/git/z3/src/api/ -L. -o z3_swi_foreign -shared z3_swi_foreign.c -lz3

