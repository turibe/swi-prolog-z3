#!/bin/sh 
swipl-ld -I./api/ -L. -o z3_swi_foreign -shared z3_swi_foreign.c -lz3

