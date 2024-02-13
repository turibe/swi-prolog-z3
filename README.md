# swi-prolog-z3

- Using Z3 as a constraint solver inside SWI Prolog, for a basic CLP(CC) implementation.

- Prolog code for Junker's explanation (minimal unsatisfiable subsets) and relaxation (maximal satisfiable subsets).


## Installation:

Tested on MacOS Sonoma.

1. Install swi-prolog. This can be done via brew, macports, or download. See [https://www.swi-prolog.org/](https://www.swi-prolog.org/).

   Provides `swipl` and `swipl-ld` executables.

2. Install and build Z3, including libz3.dylib . This can also be done via brew, macports, or download.
See [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

3. Compile the C code for the Prolog-Z3 interface, using the `swipl-ld` tool.

(Adapt the `-I` and `-L` paths accordingly.)

```bash
swipl-ld -I/Users/uribe/git/z3/src/api/ -L/Users/uribe/git/z3/build/ -o z3_swi_foreign -shared z3_swi_foreign.c -lz3
```

4. Start swipl, import the `z3.pl` module, and you're done!

```bash
swipl
?- use_module(z3).
Installing Z3 package
Using Z3 version Z3 4.12.5.0
Initializing global context
true.
```

You can now issue queries, for example:

``bash
?- z3_push(a:int=f(b) and b = 1 and f(a) > 3), z3_model(M), z3_push(f(f(a)) = 5), z3_model(M1).
M = model{constants:[a-2, b-1], functions:[f/1-else-2, f(2)-4]},
M1 = model{constants:[a-2, b-1], functions:[f/1-else-2, f(4)-5, f(2)-4]}.
```

## Quick Overview

The z3.pl module offers a high-level, user-friendly API, with:
    - Type inference, to minimize the number of declarations needed.
    - Prolog goals push assertions onto the Z3 solver, and those assertions are automatically popped when Prolog backtracks.

The type inference uses a backtrackable map too. Types can be different from one query to the next.
