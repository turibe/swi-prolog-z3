#!/bin/sh 

# You should have a symbolic link to, or copy of, libz3.dylib in this directory.

# Change the -I path to point to your Z3 install and build:

swipl-ld -I/Users/uribe/git/z3/src/api/ -L. -o z3_swi_foreign -shared z3_swi_foreign.c -lz3

