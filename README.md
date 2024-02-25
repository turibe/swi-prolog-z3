# swi-prolog-z3

Code to use Z3 as a constraint solver inside SWI Prolog, for a basic CLP(CC) implementation.
Currently supports a basic subset of Z3's capabilities,
including propositional logic, equality, arithmetic, and uninterpreted function symbols.

With the high-level API in `z3.pl`,
Z3 asserts are incremental and backtrackable, and the Z3 solver context is pushed and popped automatically.


### Contact

Tomas Uribe, t****.u****@gmail.com

Github: [https://github.com/turibe/swi-prolog-z3](https://github.com/turibe/swi-prolog-z3).


## Installation:

Tested on MacOS Sonoma.

1. Install swi-prolog. This can be done via brew, macports, or download. See [https://www.swi-prolog.org/](https://www.swi-prolog.org/).

   After this, you should have `swipl` and `swipl-ld` executables.

2. Install and build Z3, including `libz3.dylib` . This can also be done via brew, macports, or download.
See [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

Tested with Z3 version 4.12.6.0 and SWI-Prolog version 9.1.21 for arm64-darwin.

3. Add a symbolic link to the `libz3.dylib` file in this directory (or copy it over).

3. Compile the C code for the Prolog-Z3 interface, using the `swipl-ld` tool.

(Adapt the `-I` and `-L` paths accordingly.)

```bash
swipl-ld -I/<path-to-z3>/z3/src/api/ -L. -o z3_swi_foreign -shared z3_swi_foreign.c -lz3
```

This creates a `z3_swi_foreign.so` binary that is loaded into SWI Prolog when `use_module(z3)` is executed.


5. Start `swipl`, import the `z3.pl` module, and you're done!

```bash
swipl
?- use_module(z3).
Installing Z3 package
Using Z3 version Z3 4.12.5.0
Initializing global context
true.
```

You can now issue Z3 queries, for example:

```bash
?- z3_push(a:int > b:int), z3_push(b:int > a:int).
false.

?- z3_push(a:int > b:int), z3_push(b:int > c:int), z3_is_implied(a > c).
true.

?- z3_push(a:int=f(b) and b = 1 and f(a) > 3), z3_push(f(f(a)) = 5), z3_model(M).
M1 = model{constants:[a-2, b-1], functions:[f/1-else-2, f(4)-5, f(2)-4]}.
```

Unit tests can be run with `?- run_tests.` , or running

```bash
swipl -f z3.pl -g run_tests -g halt
```

## Code and Functionality Overview

### High-level, backtrackable: z3.pl

The z3.pl module offers a high-level, user-friendly API, with:
    
- Type inference, to minimize the number of declarations needed.

- Prolog goals that push assertions onto the Z3 solver, that are automatically popped when Prolog backtracks.

The type inference at this level also uses a backtrackable type map, so
both types and assertions start afresh from one query to the next. 

The basic operations are:

- `z3_push` : Typechecks and pushes a formula, as in

```prolog
z3_push(f(a:int) = b and b = 3, Status). %% Status = l_true
```

Status will be one of `{l_true, l_false, l_undef}`. One can also use `push/1`, which will fails if status is `l_false`.

- `z3_is_consistent(+Formula)`: Tests whether `Formula` is consistent with what has been pushed so far.

```prolog
?- z3_push(a > b:int), z3_is_consistent(a = 3 and b = 2). %% succeeds
?- z3_push(a > b:int), z3_is_consistent(a < c and c < b). %% fails
```

- `z3_is_implied(+Formula)`: Tests whether `Formula` is implied with what has been pushed so far.

```prolog
?- z3_push(a > b:int and b > c), z3_is_implied(a > c). %% succeeds
```

- `z3_model(-Model)` : Gets a model, if the assertions pushed so far are found to be satisfiable.

```prolog
?- z3_push(a: int > b and b = f(a) and a > f(b) and f(c:int) > a), z3_model(M).
M = model{constants:[a-0, b- -1, c-5], functions:[f/1-else- -1, f(5)-1]}.
```

- z3_eval(+Formula, -Result) : Evaluates `Formula` over a model for the assertions pushed so far, if there is one.

### Attributed Variables.

Terms with Prolog variables can be asserted as well. Prolog attributes are used to associate each variable with a fresh Z3 constant,
and new equalities will be pushed upon unification. For example:

```prolog
z3_push(X > b), z3_push(b > c), member(X, [a,b,c,d])
```
will only succeed for `X = a` and `X = d`.

### High-level, stateful: stateful_repl.pl

`stateful_repl` offers a more stateful alternative to `z3.pl`, where assertions and declarations are accumulated from one query
to the next.

The main commands are:
- add(+Formula)
- asserted(-FormulaList)
- reset
- is_implied(+Formula)
- is_consistent(+Formula)
- model(-Model)
- declarations(-Declarations)

### Lower-level: z3_swi_foreign.pl

The lower-level module has no Prolog globals.
It could be used to write an alternative to `z3.pl` that keeps state between queries,
similarly to the Python integration or the Z3 promp.

### Lowest level: z3_swi_foreign.c

The `z3_swi_foreign.c` file has the C code that glues things together, to be compiled with `swipl-ld` tool.
(See [Installation](#Installation)).

### Type inference

`type_inference.pl` has basic capabilities for inferring types for constants and functions in Prolog Z3 expressions, saving the work of having to declare everything beforehand (functions, in particular).

`type_inference_global_backtrackable.pl` uses this to implement a global backtrackable type inference map.


### Explanations and Relaxation

- We also include a generic Prolog implementation of Junker's QuickXplain algorithms,
for explanation (finding minimal unsatisfiable subsets) and relaxation (maximal satisfiable subsets).
See [https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf](https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf).
This code can be used on stand-alone basis, plugging in any monotonic `check` or `assert` predicate.
See [quickexplain.pl](https://github.com/turibe/swi-prolog-z3/blob/main/quickexplain.pl).

## Future Work

- The current version handles only the basic Z3 capabilities: {int,real,bool} types, propositional logic, equality, arithmetic, and uninterpreted function symbols.
Bit vectors, sets, and quantifiers are future work.

- A version that keeps state between queries (simple to do).

