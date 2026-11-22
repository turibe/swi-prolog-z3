# Future work

Z3 features that could be added to this integration, roughly in the suggested order.
Effort estimates are rough: small is a day or less, moderate a few days, large more.

Current support, for reference: `int`, `real` and `bool` sorts, enumerations, uninterpreted sorts and
functions, bit vectors, arithmetic, propositional logic and equality, pseudo-Boolean `atleast`/`atmost`,
and string literals.

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

### 6. Algebraic datatypes (large)

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

### 8. Quantifiers (moderate)

`forall` and `exists` over typed variables. The C side is small (`Z3_mk_forall_const`,
`Z3_mk_exists_const`), but type inference needs scoped variables, and converting terms back needs to
handle bound variables.

### 9. Floating point (moderate)

The `float` sort currently maps to Z3's reals, not IEEE floating point. Adding Z3's floating-point sorts,
with rounding modes, would matter for checking numeric code.

## Smaller conveniences

### 10. SMT-LIB2 import and export (small)

`Z3_solver_to_string` and `Z3_eval_smtlib2_string`, to dump the current assertions for other solvers or
load benchmarks.

### 11. Several solvers per handle (moderate)

Each handle bundles one solver, deliberately, to keep the Prolog side simple. Separate solvers sharing a
handle's declarations would allow independent queries without redeclaring types.

## Big numbers

### 12. GMP for big integers and rationals

See the Future Work section of the README: big numbers could be passed between Prolog and Z3 with GMP
instead of through text, mostly speeding up the way back to Prolog.

## Suggested order

1 (done), then 3, then 4: item 1 fixed silently wrong output, item 3 completes the interruption work, and item 4
builds on the existing QuickXplain code and can be checked against it. After those, 5 or 6 would most
extend what the library can do.
