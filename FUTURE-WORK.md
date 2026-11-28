# Future work

Z3 features that could be added to this integration, roughly in the suggested order.
Effort estimates are rough: small is a day or less, moderate a few days, large more.

Current support, for reference: `int`, `real` and `bool` sorts, enumerations, uninterpreted sorts and
functions, bit vectors, arithmetic (nonlinear too, with exact irrational values in models), propositional
logic and equality, pseudo-Boolean `atleast`/`atmost`, strings, arrays, quantifiers and IEEE floating
point; unsat cores, explanations and relaxations, optimization, timeouts and interrupts; SMT-LIB2 import
and export; algebraic datatypes; and Prolog variables in formulas, with `z3_label/1`. Still open:
items 11 and 12, the leftovers listed under the items that are done, and items 13 to 17.

## Gaps in what is already there

### 1. Irrational values in models (done)

Irrational values now appear as `algebraic(Approx, root(Coefficients, Index))`; see the README.
What follows describes the problem as it was.


With nonlinear real arithmetic, a model can contain an irrational number, and it is currently lost:

```prolog
?- z3_push(x:real * x:real = 2.0), z3_push(x > 0.0), z3_model(M).
M = model{constants:[x='RootObject'], functions:[]}.
```

Z3 can give a decimal approximation (`Z3_get_numeral_decimal_string`) or bounds
(`Z3_get_algebraic_number_lower` / `Z3_get_algebraic_number_upper`). Returning one of those, or a term
such as `root(Polynomial, Index)` for the exact value, would replace the silent `'RootObject'`.

### 2. A string sort and string operations (done, except regular expressions)

There is now a `string` sort, with the operations listed under Reserved names in the README
(`str_len`, `str_concat`, `str_contains`, ...). Strings are passed by code point, so non-ASCII
characters and backslashes are kept exactly. Regular expressions (`Z3_mk_re_*`, `Z3_mk_seq_in_re`)
are still to do. What follows describes the problem as it was.


String literals are converted to Z3 strings, but there is no `string` sort, so `s:string` creates an
unrelated uninterpreted sort:

```prolog
?- z3_push(s:string = "abc").
ERROR: different types for equals, failing
ERROR: sort1: string
ERROR: sort2: String
```

Add the sort, then the basic operations: length, concatenation, substring, `contains`, `indexof`,
conversion to and from integers, and later regular expressions.

## New solver capabilities

### 3. Timeouts and interrupts (done)

There is now `z3_set_timeout/1,2`, `z3_interrupt/1` and `z3_reason_unknown/1,2`, and a running
`z3_check` responds to `call_with_time_limit/2`, `thread_signal/2` and Ctrl-C; see the README.
What follows describes the problem as it was.


A solver `timeout` parameter, and a `z3_interrupt/1` predicate built on `Z3_interrupt`, which is safe to
call from another thread. This would complete the work on busy handles: a thread waiting for a handle
can already be interrupted (by `call_with_time_limit/2`, `thread_signal/2` or Ctrl-C), but a running
`z3_check` cannot, since it only sees Prolog signals after Z3 returns.

### 4. Unsat cores and checking under assumptions (done)

There is now `z3_unsat_core/2` and `z3_minimal_core/2` in `z3.pl`, and `z3_check_assumptions/3` and
`z3_get_unsat_core/2` at the lower level; see the README. On 203 formulas with a conflict among 3 of
them, `z3_minimal_core/2` gives the same result as QuickXplain alone, about 14 times faster.
What follows describes the plan as it was.


`Z3_solver_assert_and_track`, `Z3_solver_check_assumptions` and `Z3_solver_get_unsat_core`.
`quickexplain.pl` finds minimal conflicting subsets with repeated push, check and pop; a native unsat
core would give it a fast first approximation, or replace it in simple cases, and could be tested
against it.

### 5. Optimization (done)

There is now a one-shot `z3_optimize/2` in `z3.pl`, and `z3_optimize/5` at the lower level, with
`minimize`, `maximize` and weighted soft constraints; see the README. A persistent, incremental
optimizer per handle was not added. What follows describes the plan as it was.


`Z3_optimize`: `minimize` and `maximize` objectives, and weighted soft constraints. Today only
satisfiability can be checked, so this would open up problems such as scheduling and assignment. It needs
a second kind of object beside the solver, probably held by the handle.

## More of Z3's logic

### 6. Algebraic datatypes (done)

There is now `z3_declare_datatype/2` and `z3_declare_datatypes/1` (for mutual recursion), with
constructors, `is_C` recognizers and accessors, constructor terms in models, and datatypes in
SMT-LIB2 import; see the README. Not done: parametric datatypes (`list(T)`), and fields whose sort
contains a datatype being declared (`array(int, tree)`). What follows describes the plan as it was.


`Z3_mk_datatype`: records, lists and trees. They map naturally onto Prolog terms, so `cons(H, T)` could be
a real Z3 datatype rather than an uninterpreted function. Needs a declaration syntax, constructors,
accessors and recognizers, and conversion of datatype values back to Prolog.

### 7. Arrays (done)

There is now an `array(IndexSort, ValueSort)` sort, with `select/2`, `store/3` and `const_array/2`; model
values are `store` chains over `const_array`, as Z3 gives them, and can be used in formulas again; see the
README. Not handled: array values that Z3 gives as references to a function interpretation (`as-array`),
which did not occur without quantifiers. What follows describes the plan as it was.


`select` and `store`, with an `array(Index, Value)` sort. Mostly sort handling and type inference in
`type_inference.pl`, plus converting array values in models back to Prolog.

### 8. Quantifiers (done)

There is now `forall(Vars, Body)` and `exists(Vars, Body)`, with scoped bound variables in type inference
and in the C conversion, and quantified assertions converted back to Prolog; see the README. Not added:
patterns (triggers) for quantifier instantiation, and lambda terms. What follows describes the plan as it was.


`forall` and `exists` over typed variables. The C side is small (`Z3_mk_forall_const`,
`Z3_mk_exists_const`), but type inference needs scoped variables, and converting terms back needs to
handle bound variables.

### 9. Floating point (done)

Z3's IEEE floating-point sorts, with rounding modes, operations, conversions and exact values in models
(see the README). The `float` and `double` sort names, which meant reals, are now errors. Not done: bit
vectors to floating point by `fp(Sign, Exponent, Significand)`, and optimizing floating-point terms,
which Z3 does not support.

## Smaller conveniences

### 10. SMT-LIB2 import and export (done)

There is now `z3_smtlib2/1`, `z3_push_smtlib2/1` and `z3_smtlib2_formulas/2` in `z3.pl`, and
`z3_solver_smtlib2/2`, `z3_parse_smtlib2/4` and `z3_eval_smtlib2/2` at the lower level; see the README.
Enumeration sorts are imported; other datatypes wait for item 6. What follows describes the plan as it
was.


`Z3_solver_to_string` and `Z3_eval_smtlib2_string`, to dump the current assertions for other solvers or
load benchmarks.

### 11. Several solvers per handle (moderate)

Each handle bundles one solver, deliberately, to keep the Prolog side simple. Separate solvers sharing a
handle's declarations would allow independent queries without redeclaring types.

## Big numbers

### 12. GMP for big integers and rationals

See the Future Work section of the README: big numbers could be passed between Prolog and Z3 with GMP
instead of through text, mostly speeding up the way back to Prolog.

## Found while working on the above

### 13. Making the solver state follow backtracking with undo/1 (blocked)

`z3.pl` keeps Z3's scopes in step with Prolog's backtracking with a backtrackable depth counter, which
every predicate that reads the solver must resolve first. SWI-Prolog's `undo/1` could do this directly:
each push would register its pop, and each push's new declarations their removal, so Z3's state would
follow the current branch with nothing to resolve. A version of `z3.pl` that does this is on the local
`undo-solver` branch. It cannot be merged yet: with SWI-Prolog 11.0.0, an undo goal can be lost (under
plunit, a test with a `true(...)` option after exactly two tests runs only one of its two), which leaves
declarations behind; and with 9.1.21, a clause that registers an undo goal and then fails crashes the
VM. The branch has a minimal reproduction (`test/undo_lost.pl`) and an issue description
(`test/undo_lost_issue.md`) for the SWI-Prolog maintainers. Revisit when `undo/1` is reliable.

### 14. Enumeration sorts in the stateful REPL (small)

`stateful_repl.pl` has no command to declare an enumeration sort, and `decl/1` shows Z3's sort names
(`'Int'`) next to the Prolog ones (`int`).

### 15. Quieter error output in the tests (small)

`make test` prints about 40 expected `ERROR:` and `INFO:` lines from tests of error handling, which the C
code writes straight to stderr. A flag to turn these messages off, or routing them through Prolog's
message system, would let the tests hide them.

### 16. Tests that depend on what is loaded (small)

Two `finalize_memory` tests fail when `z3_swi_foreign.pl` is loaded without `z3.pl` (for example, when
running all the tests from `examples/pigeonhole.pl`); `make test`, which loads both, passes. The cause is
not known yet.

### 17. The `:` operator (design)

`z3.pl` and `stateful_repl.pl` export `:` at priority 299, so that `x:int` binds tighter than `+` and
`=`. Where they are loaded, module-qualified predicate indicators need parentheses, as in
`lists:(append/3)`. This is documented in the README; avoiding it would mean another annotation syntax.

## Found while writing the Sudoku, knights-and-knaves and bit tricks examples

### 18. More bit-vector operations (small)

There is no `zero_extend`, `sign_extend`, `extract`, `concat` (of bit vectors) or `rotate_left` /
`rotate_right`. Without them, a formula cannot widen a word to check for overflow, or take bits out of
it. `examples/bit_tricks.pl` gets around this for the overflow-free average by using 64-bit values
below 2^32, so that `x + y` is exact; with `zero_extend`, it could compare 32-bit values with their
33-bit sum directly. These take their widths as parameters (`Z3_mk_zero_ext(ctx, i, t)`,
`Z3_mk_extract(ctx, high, low, t)`), so, like `int2bv/2`, they need a case in `z3_swi_foreign.c` as
well as signatures in `type_inference.pl` (see Reserved names in the README).

### 19. Plain numbers in bit-vector formulas (small, design)

A bit-vector numeral has to be written `int2bv(Width, N)`: `bvxor(x:bv(32), 0)` is a type error, so
formulas with many constants are hard to read. `examples/bit_tricks.pl` has a helper, `bits/3`, that
rewrites the plain numbers of a formula into `int2bv/2`. Type inference could do the same, giving an
integer literal the bit-vector sort that its context requires. The catch: the same literal could then mean
an integer or a bit vector depending on where it is, which would also change how models and exported
formulas are read back.

### 20. Mixing integers and bit vectors is slow (known Z3 behavior; documentation)

Formulas that convert between the two with `bv2int` (or `int2bv` on non-constant terms) can make Z3
very slow: proving the overflow-free average, as `bv2int(Average, false) = (bv2int(x, false) +
bv2int(y, false)) div 2`, did not finish in a minute, against 0.01 s for the same property in pure
64-bit bit vectors. The README's bit-vector section could say so, and suggest staying within bit
vectors (with a wider width, or `zero_extend` once 18 is done).

### 21. Integer encodings of finite domains are slow (known Z3 behavior; documentation)

Integers from 1 to 9 are a poor encoding for Sudoku-like problems: Z3 5.4.1 takes 20 to 25 s to find
any 9x9 Latin square (distinct rows and columns) over them, and the time grows quickly with the size
(1 s for 7x7, 5 s for 8x8). An enumeration sort or 4-bit bit vectors take a few hundredths of a
second. This is not incremental mode: one check of the whole problem is just as slow. It matters more
in `z3.pl` than elsewhere, since every `z3_push` runs a check, so a problem's rules are solved before
its data (such as the clues) are pushed; pushing the data first helps. `examples/smt2/` has the Latin
square in the three encodings, with a script that times them, and `examples/sudoku.pl` explains its
choice of an enumeration sort. The README could mention this next to enumeration sorts.

### 22. Pushing inside forall/2 does nothing (documentation)

`z3_push/1` is undone on backtracking, like a Prolog binding, so `forall(member(F, Fs), z3_push(F))`,
or any failure-driven loop, leaves nothing pushed, silently: the Sudoku example first returned grids
that broke every rule because of this. It follows from the design, but it is an easy mistake. The README
could warn about it and show the alternatives, `maplist(z3_push, Fs)` or one pushed conjunction.

### 23. z3_push/1 fails at the end of an enumeration (documentation)

Enumerating solutions by blocking each model with `z3_push(not(...))` ends with that push failing, since
the last block makes the formulas inconsistent. A loop written with `z3_push/1` then fails as a whole,
instead of stopping. `z3_push/2`, which gives the status, is the one to use; `count_solutions/3` in
`examples/sudoku.pl` does. `z3_label/1` covers the common case; a predicate that enumerates or counts
models of a list of terms (with a limit) might be worth adding, since blocking clauses are a common
idiom.

### 24. Synthesis with forall over bit vectors can be slow (observation)

Finding a constant with an exists-forall query works well for small widths: the multiplier that divides
8-bit numbers by 3, with 16-bit arithmetic, takes hundredths of a second. The 32-bit version (16-bit
numbers, multiplier 43691, shift 17) takes about 10 s, so `examples/bit_tricks.pl` uses the small one.
Nothing to fix; worth knowing when writing such queries, together with a timeout.

## Suggested order

With 6 and 10 done, the small items, 14 to 16, can be done at any time, and parametric datatypes
(a leftover of 6) when needed; 11 when
independent queries on shared declarations are needed; and 13 when SWI-Prolog's `undo/1` is fixed.
Of the newer items, 18 is the most useful, and 20 to 23 are documentation that can go into the README
together.
