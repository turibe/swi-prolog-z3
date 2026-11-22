# swi-prolog-z3

Code to use Z3 as a constraint solver inside SWI Prolog, for a CLP(CC) implementation.
Currently supports a subset of Z3's capabilities,
including propositional logic, equality, arithmetic, bit-vectors, and uninterpreted function symbols.

With the high-level API in `z3.pl`,
Z3 asserts are incremental and backtrackable, and the Z3 solver context is pushed and popped automatically.

Alternatively, `stateful-repl` accumulates state from one query to the next.

### Contact

Tomas Uribe, t****.u****@gmail.com

Github: [https://github.com/turibe/swi-prolog-z3](https://github.com/turibe/swi-prolog-z3).


## Installation:

Tested on macOS (arm64) with SWI-Prolog 9.1.21 and Z3 5.4.2 (built from source with CMake),
Z3 5.4.1 (Homebrew), and Z3 4.12.6.

1. Install swi-prolog. This can be done via brew, macports, or download. See [https://www.swi-prolog.org/](https://www.swi-prolog.org/).

   After this, you should have `swipl` and `swipl-ld` executables.

2. Get Z3, either from Homebrew or by building it from source. See [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

   - Homebrew: `brew install z3`. The headers are then in `/opt/homebrew/include` and the library in `/opt/homebrew/lib`.
   - From source, with CMake (this needs `cmake` and `ninja`, for example from Homebrew):

     ```bash
     git clone https://github.com/Z3Prover/z3.git ~/git/z3
     cd ~/git/z3
     cmake -S . -B build-cmake -G Ninja -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_TEST_EXECUTABLES=OFF
     ninja -C build-cmake libz3
     ```

     This creates `build-cmake/libz3.dylib`; the headers are in `src/api`.
     If an older build with Z3's Python script left generated `*.hpp` files in the source tree
     (such as `src/sat/sat_params.hpp` or `src/smt/params/smt_params_helper.hpp`), delete them first:
     they shadow newer headers and break the build.

3. Tell the build where Z3 is. Either add a symbolic link to `libz3.dylib` in this directory:

   ```bash
   ln -s ~/git/z3/build-cmake/libz3.dylib libz3.dylib
   ```

   or set `Z3_LIBDIR` to the directory holding `libz3.dylib` in the next step.
   After switching to a different Z3, run `make clean` before `make`, so the library is relinked against it.

4. Compile the C code for the Prolog-Z3 interface with `make`.
By default it looks for the Z3 headers in `~/git/z3/src/api` and for `libz3.dylib` in this directory;
set `Z3_INCLUDE` and `Z3_LIBDIR` to point elsewhere:

```bash
make                                                               # Z3 source in ~/git/z3, symlink here
make Z3_INCLUDE=/opt/homebrew/include Z3_LIBDIR=/opt/homebrew/lib  # Homebrew
```

This runs `swipl-ld` and creates a `z3_swi_foreign.so` binary that is loaded into SWI Prolog when `use_module(z3_swi_foreign)` is executed.
On macOS, `make` also records where `libz3.dylib` is (next to `z3_swi_foreign.so` for the default `Z3_LIBDIR`),
so the library loads from any working directory. This works with Z3 built by its Python script or by CMake,
and with Homebrew's Z3, which already records an absolute path.

5. Start `swipl`, import the `z3.pl` or `stateful_repl.pl` module (e.g. `use_module(z3)`), and you're done!

```bash
swipl
?- use_module(z3).
Using Z3 version 5.4.2.0 ...
true.
```

You can now issue Z3 queries, for example:

```bash
?- z3_push(a:int > b:int), z3_push(b:int > a:int).
false.

?- z3_push(a:int > b:int), z3_push(b:int > c:int), z3_is_implied(a > c).
true.

?- z3_push(a:int=f(b) and b = 1 and f(a) > 3), z3_push(f(f(a)) = 5), z3_model(M).
M = model{constants:[a=2, b=1], functions:[f(2)=4, f(4)=5, (f/1=else)=2]}.
```

With nonlinear real arithmetic, a model can contain irrational values. These appear as
`algebraic(Approx, root(Coefficients, Index))`: `Approx` is a float, and the exact value is the
`Index`-th smallest real root of the polynomial with integer `Coefficients`, lowest degree first:

```bash
?- z3_push(x:real * x:real = 2.0 and x > 0.0), z3_model(M).
M = model{constants:[x=algebraic(1.4142135623730951, root([-2, 0, 1], 2))], functions:[]}.
```

Here `[-2, 0, 1]` is x^2 - 2, and index 2 picks its larger root, the positive square root of 2.

Such terms can also be used in formulas, where they denote the exact root; `Approx` is ignored,
so a value from one model can be pushed into another query:

```bash
?- z3_push(y:real = algebraic(1.4142135623730951, root([-2, 0, 1], 2))), z3_is_implied(y * y = 2.0).
true.
```

This makes `algebraic/2` a reserved name, like the other built-in operations.
[examples/algebraic_numbers.pl](examples/algebraic_numbers.pl) has worked examples: the golden ratio, cube and square roots, a root that cannot be written with
radicals, and exact values against floats. Run it with
`./examples/algebraic_numbers.pl`.

6. If you prefer, run `use_module(stateful_repl)` and add assertions interactively:
```bash
?- add(a:int > 1).
?- add(a > b).
?- model(M).
M = model{constants:[a=2, b=0], functions:[]}.
```

## Testing

Unit tests can be run from the PL prompt with `?- run_tests.` , or with `make test`, which rebuilds the library if needed and then runs

```bash
swipl -g run_tests -t halt z3.pl stateful_repl.pl z3_swi_foreign.pl
```

On macOS, `make leaks` checks the C code for memory leaks. It runs a workload that exercises most of
`z3_swi_foreign.c` (`test/leaks.pl`) under macOS's `leaks` tool, and fails if any leaked block was
allocated from `z3_swi_foreign.so`. Set `LEAK_ITERATIONS` to change the workload size (default 100;
every line and branch of the C code that the workload reaches is already reached in 100 iterations).
It finds memory that is never freed, not objects that are kept alive longer than needed but are freed
with their handle.

## Examples

[examples/](examples/README.md) has worked examples of each feature, as scripts that print
questions and Z3's answers; its README shows how to run them, explore them interactively, and run
their tests.

## Code and Functionality Overview

### High-level, backtrackable: z3.pl

The z3.pl module offers a high-level, user-friendly API, with:
    
- Type inference, to minimize the number of declarations needed.

- Prolog goals that push assertions onto the Z3 solver, that are automatically popped when Prolog backtracks.

The type inference at this level also uses a backtrackable type map, so
both types and assertions start afresh from one query to the next.
(If you don't want this, see stateful_repl.pl.)

The basic operations are:

- `z3_push` : Typechecks and pushes a formula, as in

```prolog
z3_push(f(a:int) = b and b = 3, Status). %% Status = l_true
```

Status will be one of `{l_true, l_false, l_undef, l_type_error}`.
One can also use `z3_push/1`, which fails if status is `l_false` or `l_type_error`.

- `z3_is_consistent(+Formula)`: Tests whether `Formula` is consistent with what has been pushed so far.

```prolog
?- z3_push(a > b:int), z3_is_consistent(a = 3 and b = 2). %% succeeds
?- z3_push(a > b:int), z3_is_consistent(a < c and c < b). %% fails
```

- `z3_is_implied(+Formula)`: Tests whether `Formula` is implied by what has been pushed so far.

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

With `z3.pl`, all assertions and type declarations (except for enums) are reset from one query to the
next. The `stateful_repl` module is an alternative where formulas and declarations accumulate from one
query to the next, as with the Z3 prompt or the Python API:

```prolog
?- use_module(stateful_repl).
?- add(x:int > 3).
?- add(y = x + 1).
?- implied(y > 4).
true.
?- consistent(y < 4).
false.
?- model(M).
M = model{constants:[x=4, y=5], functions:[]}.
```

`add(F)` type-checks `F` against the types so far, declares its new symbols, and keeps `F` only if it is
consistent with the formulas added before; otherwise it fails, and nothing changes. This holds too if
the check is stopped (by `call_with_time_limit/2` or Ctrl-C). If Z3 cannot decide (status `l_undef`,
for example after a timeout), `F` is added, with a warning. `z3_help/0` lists the commands:

- Adding and asking:
  - `add(+F)`: add formula `F`.
  - `implied(+F)` (or `implies/1`): `F` follows from the formulas added so far.
  - `consistent(+F)`: `F` is consistent with them. Like `implied/1`, it fails if Z3 cannot decide.
  - `model(-M)`: a model of the formulas added so far.
- State:
  - `formulas(-L)` (or `asserted/1`): the formulas added so far, in order.
  - `declarations(-L)`: the types of the symbols so far; `decl/1` also shows Z3's declarations.
  - `status(-S)`: `l_true`, `l_false` or `l_undef`.
  - `show_status/0`: prints the number of formulas, the status and the number of declarations.
  - `scopes(-N)`: the number of solver scopes, one per formula added.
  - `reset/0`: removes all formulas and declarations.
- Timeouts: `timeout(+Ms)` limits each check to `Ms` milliseconds (0 for no limit; `reset/0` keeps it),
  and `reason_unknown(-R)` says why the last check had status `l_undef`.
- Conflicts and optimization, relative to the formulas added so far, without adding anything:
  - `unsat_core(+Fs, -Core)`: a subset of `Fs` that conflicts with them;
  - `explain(+Fs, -Core)`: a minimal such subset;
  - `relax(+Fs, -Kept)`: a maximal subset of `Fs` consistent with them, preferring earlier formulas;
  - `optimize(+Objectives, -M)`: a model that is best for `Objectives` (see Optimization).

  These use `z3.pl` (`z3_unsat_core/2` and so on), with the formulas added so far pushed first. They
  run inside `findall/3`, so `z3.pl`'s own formulas are unaffected, but don't call them while you
  have `z3.pl` formulas pushed in the same query.
- Sessions: `save_formulas(+File)` saves the formulas added so far, and `add_formulas(+File)` adds
  the formulas saved in `File`.

Like `z3.pl`, `stateful_repl` exports the operators `and`, `or`, `<>`, `<=>`, and `:` at priority 299,
so that `x:int` binds tighter than `+` and `=`. A consequence is that, where it is loaded, a
module-qualified predicate indicator needs parentheses: `lists:(append/3)`.

### Lower-level: z3_swi_foreign.pl

The lower-level `z3_swi_foreign.pl` module has no Prolog globals.
It is used by both `z3.pl` and `stateful_repl.pl`.

### Lowest level: z3_swi_foreign.c

The `z3_swi_foreign.c` file has the C code that glues things together, to be compiled with `swipl-ld` tool.
(See [Installation](#Installation)).

### Type inference

`type_inference.pl` has basic capabilities for inferring types for constants and functions in Prolog Z3 expressions, saving the work of having to declare everything beforehand (functions, in particular).

`type_inference_global_backtrackable.pl` uses this to implement a global backtrackable type inference map.

### Enumerated types

Finite-domain enumerated types are "sticky" in Z3, and are declared with
```
z3_declare_enum(+enum_name, +values_list)
```
For example, `z3_declare_enum(fruit, [apple, banana, pear])`.
The associated declarations can be listed with `z3_enum_declarations`.
To clear them, we must reset the entire Z3 context,
with `z3_reset_context` (low-level), `z3_reset` (for `z3.pl`), or `reset` (for `stateful_repl.pl`).

### Utilities/shortcuts

For convenience, we expand `isoneof(a,v1,...,vn)` to `or(a=v1, ... a=vn)`.

`alldifferent` is an alias for Z3's `distinct`.

### Timeouts and interrupts

A long check can be stopped in several ways:

- `z3_set_timeout(Milliseconds)` (or `z3_set_timeout(Handle, Milliseconds)` with `z3_swi_foreign`)
  limits each check; one that runs out has status `l_undef`. 0 removes the limit.
- `call_with_time_limit/2`, `thread_signal/2` and Ctrl-C stop a running check and raise their
  exception, as for any other Prolog goal.
- `z3_interrupt(Handle)`, from another thread, makes a running check return `l_undef`.

After an `l_undef` status, `z3_reason_unknown(Reason)` says why: for example `timeout` or `canceled`
for a timeout, or `interrupted` after `z3_interrupt/1`.

```prolog
?- z3_set_timeout(1000), z3_push(HardFormula, Status), z3_reason_unknown(Reason).
Status = l_undef, Reason = timeout.       % or canceled, depending on which part of Z3 stops
```

[examples/timeouts.pl](examples/timeouts.pl) has worked examples: a timeout, `call_with_time_limit/2`, `z3_interrupt/1` from another thread, and
the solver still working afterwards, all on a pigeonhole problem. Run it with
`./examples/timeouts.pl`.

### Optimization

`z3_optimize(Objectives, Model)` finds a model of the formulas pushed so far that is optimal for
`Objectives`, a list in priority order (earlier objectives take precedence) of:

- `minimize(T)` and `maximize(T)`, for an arithmetic or bit-vector term `T`;
- `soft(F)` and `soft(F, Weight)`, for a formula `F` that should hold if possible, with a positive
  integer or float `Weight` (1 by default). All soft constraints together form one objective, at the
  position of the first one, minimizing the total weight of those that are violated.

The model has an extra key, `objectives`, with each objective's value: the optimum, or for a soft
constraint whether it holds.

```prolog
?- z3_push(x:int >= 0 and y:int >= 0 and x + y =< 10), z3_optimize([maximize(2*x + y)], M).
M = model{constants:[x=10, y=0], functions:[], objectives:[maximize(2*x+y)=20]}.
```

Optima can be infinite or not attained, so values can contain `oo` (infinity) and `epsilon` (an
infinitesimal): `maximize(x) = oo` when `x` is unbounded, or `minimize(x) = epsilon` for `x > 0` over the
reals. `z3_optimize/2` fails if the formulas are inconsistent, or if Z3 cannot decide (for example after a
timeout). At the lower level, `z3_optimize(Handle, Objectives, Status, Values, Model)` returns the status,
the values and a model of the handle's solver.

[examples/optimization.pl](examples/optimization.pl) has worked examples: a production plan, a knapsack, lexicographic priorities, weighted
preferences, and unbounded objectives. Run it with
`./examples/optimization.pl`.

### Arrays

Arrays have the sort `array(IndexSort, ValueSort)`, and are used with `select/2`, `store/3` and
`const_array/2` (see Reserved names). In models, an array's value is a chain of `store` terms over a
constant array, which can be used in formulas again:

```prolog
?- z3_push(select(a:array(int, int), 1) = 5), z3_push(select(a, 2) = 7), z3_model(M).
M = model{constants:[a=store(const_array(int, 7), 1, 5)], functions:[]}.
```

Here every element of `a` is 7, except the one at index 1. (Z3 chose 7 for the default, since only
indices 1 and 2 are constrained.)

[examples/arrays.pl](examples/arrays.pl) has worked examples: finding arrays, swapping elements, which stores commute, a lookup table,
and a matrix as an array of arrays. Run it with
`./examples/arrays.pl`.

### Quantifiers

`forall(Vars, Body)` and `exists(Vars, Body)` quantify over `Vars`, a list of names, each optionally with a
sort (`x:int`); `z3.pl` infers the sorts of the others from the body. Inside the body, a bound name
refers to the bound variable, shadowing any constant of the same name; bound names are not declared as
constants.

```prolog
?- z3_push(forall([x], f(x) = 2 * x)), z3_is_implied(f(5) = 10).
true.
```

Z3 is good at proving that a quantified formula is unsatisfiable, by instantiating its quantifiers, but
it cannot always decide that one is satisfiable: `forall([x:int], f(x) > x)` holds for `f(x) = x + 1`,
yet Z3 searches until stopped. Since `z3_push` checks after each push, set a timeout (`z3_set_timeout/1`)
when using quantifiers; an undecided check then has status `l_undef`. At the lower level
(`z3_swi_foreign`), each bound variable needs its sort.

In a model, a function defined by a quantifier can have an else value that depends on its arguments;
it is then a `lambda(Args, Body)`, with the arguments named as Z3 prints them:

```prolog
?- z3_push(forall([a:int, b:int], g(a, b) = a - b)), z3_model(M).
M = model{constants:[], functions:[(g/2=else)=lambda(['x!0':int, 'x!1':int], 'x!0'+ -1*'x!1')]}.
```

[examples/quantifiers.pl](examples/quantifiers.pl) has worked examples: a syllogism, properties of
functions and arrays, defining a function by an axiom, explaining an inconsistency, and a question Z3
cannot settle. Run it with `./examples/quantifiers.pl`.

### Floating point

IEEE floating point has the sorts `float16`, `float32`, `float64` and `float128`, and `fp(Ebits, Sbits)`
for other formats (`float32` is `fp(8, 24)`). It is not the reals: every operation rounds, and there
are infinities, NaN and two zeros. This is what to use for checking numeric code. The names follow
SMT-LIB, with an `fp_` prefix, and the rounding mode first:

- Rounding modes, of sort `roundingmode`: `rne` (to nearest, ties to even: the usual one), `rna` (to
  nearest, ties away from zero), `rtp` and `rtn` (toward positive or negative infinity), `rtz` (toward
  zero).
- Constants: `fp_value(Value, Sort)`, the value of `Sort` nearest to `Value` (an integer, a float, a
  rational, `nan`, `inf` or `-inf`), so `fp_value(0.1, float32)` is C's `0.1f`.
- Arithmetic: `fp_add(RM, X, Y)`, `fp_sub`, `fp_mul`, `fp_div`, `fp_fma(RM, X, Y, Z)` (`X * Y + Z`,
  rounded once), `fp_sqrt(RM, X)`, `fp_round_to_integral(RM, X)`, `fp_rem(X, Y)` (the IEEE remainder),
  `fp_abs/1`, `fp_neg/1`, `fp_min/2`, `fp_max/2`.
- Comparisons: `fp_eq`, `fp_lt`, `fp_leq`, `fp_gt`, `fp_geq`. `fp_eq` is IEEE equality, as C's `==`: NaN
  is not `fp_eq` to itself, and `0.0` and `-0.0` are. `=` is identity: NaN `=` NaN, and the two zeros
  differ. `+`, `<` and the other arithmetic operators are for `int` and `real` only.
- Tests: `fp_is_nan`, `fp_is_infinite`, `fp_is_zero`, `fp_is_normal`, `fp_is_subnormal`,
  `fp_is_negative`, `fp_is_positive`.
- Conversions: `to_fp(RM, X, Sort)` from a real, an integer, another floating-point number or a signed bit
  vector; `to_fp_unsigned(RM, BV, Sort)`; `fp_to_real(X)`; `fp_to_sbv(RM, X, Width)` and
  `fp_to_ubv(RM, X, Width)`, to signed or unsigned bit vectors (as C's casts to integer types, with
  `rtz`); `fp_to_ieee_bv(X)` and `fp_from_ieee_bv(BV, Sort)`, to and from the IEEE bits.

Models give values as `fp_value(Value, Sort)` too, which can be pushed again with the same meaning. For
formats that fit in a double (`float16`, `float32`, `float64`), `Value` is a Prolog float with exactly
the model's value (`-0.0` included); for larger ones, it is an exact integer or rational.

```prolog
?- z3_push(fp_add(rne, x:float32, fp_value(0.1, float32)) = fp_value(0.3, float32)), z3_model(M).
M = model{constants:[x=fp_value(0.20000001788139343, float32)], functions:[]}.

?- z3_is_implied(fp_add(rne, fp_add(rne, a:float16, b:float16), c:float16)
                 = fp_add(rne, a, fp_add(rne, b, c))).
false.      % not associative
```

The sort names `float` and `double` used to mean `real`. They are now errors, so that neither meaning
is assumed: use `real`, or one of the floating-point sorts above (`float64` is C's `double`, and
`float32` its `float`).

Z3 decides floating-point questions by reasoning about the bits, so larger formats are slower: a
question that takes seconds with `float64` may take a fraction of one with `float16`, which has the same
pitfalls. `z3_optimize/2` does not optimize floating-point terms (minimizing `fp_to_real(X)` runs until
stopped). A model with conversions such as `fp_to_sbv` lists Z3's function for their unspecified
results (for NaN, or out of range), under Z3's own name.

[examples/floating_point.pl](examples/floating_point.pl) has worked examples: `0.1 + 0.2`, a number not
equal to itself, where `x + 1 = x`, rounding modes, associativity and summation order, an overflowing
midpoint and its fixes, and `sqrt(x * x)`. Run it with `./examples/floating_point.pl`.

### Reserved names

These names have a built-in meaning in formulas, so they cannot be used as names of your own
constants or functions (with the arities shown, where they matter).

- Special forms:
  - `Term:Sort`, a type annotation;
  - `algebraic/2`, an algebraic number, `algebraic(Approx, root(Coefficients, Index))` (every `algebraic/2` term is read as one);
  - `bv_numeral/1`, a bit vector from a list of bits;
  - `mk_numeral/2` and `mk_unsigned_int64/2`, a numeral of a given sort;
  - `int2bv/2` and `bv2int/2`, conversions between integers and bit vectors;
  - `mk_rational/2`, a rational from a numerator and a denominator;
  - `fp_value/2`, a floating-point constant;
  - `isoneof/N` and `alldifferent/N`, macros (see above).
- Constants: `true`, `false`, and the rounding modes `rne`, `rna`, `rtp`, `rtn`, `rtz`.
- Sort names, in `Term:Sort` and declarations: `int` or `integer`, `real`, `bool` or `boolean`, `bv(N)`,
  `string`, `array(IndexSort, ValueSort)`, `float16`, `float32`, `float64`, `float128`, `fp(Ebits, Sbits)`,
  `roundingmode`, and the names of declared enumeration sorts. `float` and `double` are errors (they
  used to mean `real`).
  Any other atom names an uninterpreted sort.
- Logic: `and`, `or`, `not`, `implies`, `iff`, `xor`, `ite`, and the operators `,`, `;`, `->`, `<=>`.
- Equality and comparison: `=`, `==`, `equal`, `equals`, `<>`, `distinct`, `<`, `>`, `=<`, `>=`,
  `leq`, `geq`, `between`.
- Arithmetic: `+`, `-`, `minus`, `*`, `/`, `div`, `mod`, `rem`, `divides`, `power`, `**`, `^`,
  `is_int`, `int2real`, `real2int`.
- Pseudo-Boolean: `atleast`, `atmost`.
- Quantifiers: `forall(Vars, Body)` and `exists(Vars, Body)`.
- Arrays: `select(Array, Index)`, `store(Array, Index, Value)` (the array with `Index` set to `Value`), and
  `const_array(IndexSort, Value)` (the array with `Value` at every index).
- Strings, with arguments in the SMT-LIB order: `str_concat/N`, `str_len/1`, `str_substr/3` (string, offset,
  length), `str_at/2` (the one-character string at an index), `str_contains/2` (container, containee),
  `str_prefixof/2` and `str_suffixof/2` (prefix or suffix first), `str_indexof/3` (string, substring, start;
  -1 if absent), `str_replace/3` (the first occurrence), `str_lt/2` and `str_le/2` (lexicographic),
  `str_to_int/1` (-1 unless all digits), `int_to_str/1` ("" for negative numbers).
  [examples/strings.pl](examples/strings.pl) has worked examples: a password, a word equation, splitting an
  email address, digits, Unicode and lexicographic order.
- Floating point (see above): `fp_add`, `fp_sub`, `fp_mul`, `fp_div`, `fp_fma`, `fp_sqrt`, `fp_rem`,
  `fp_round_to_integral`, `fp_abs`, `fp_neg`, `fp_min`, `fp_max`, `fp_eq`, `fp_lt`, `fp_leq`, `fp_gt`,
  `fp_geq`, `fp_is_nan`, `fp_is_infinite`, `fp_is_zero`, `fp_is_normal`, `fp_is_subnormal`,
  `fp_is_negative`, `fp_is_positive`, `to_fp/3`, `to_fp_unsigned/3`, `fp_to_real/1`, `fp_to_sbv/3`,
  `fp_to_ubv/3`, `fp_to_ieee_bv/1`, `fp_from_ieee_bv/2`.
- Bit vectors:
  - arithmetic: `bvadd`, `bvsub`, `bvmul`, `bvudiv`, `bvsdiv`, `bvurem`, `bvsrem`, `bvsmod`, `bvneg`;
  - bitwise: `bvand`, `bvor`, `bvxor`, `bvnand`, `bvnor`, `bvxnor`, `bvnot`, `bvredand`, `bvredor`;
  - shifts: `bvshl`, `bvlshr`, `bvashr`;
  - comparisons: `bvult`, `bvule`, `bvugt`, `bvuge`, `bvslt`, `bvsle`, `bvsgt`, `bvsge`;
  - overflow checks: `bvadd_no_overflow/3`, `bvadd_no_underflow/2`, `bvsub_no_overflow/2`,
    `bvsub_no_underflow/3`, `bvmul_no_overflow/3`, `bvmul_no_underflow/2`, `bvneg_no_overflow/1`,
    `bvsdiv_no_overflow/2` (in the three-argument forms, the last argument says whether the check is signed).

Two places know these names: `type_inference.pl`, which types formulas for `z3.pl`, and the conversion in
`z3_swi_foreign.c`. A name added to one should be added to the other.

### Explanations and Relaxation

- We also include a generic Prolog implementation of Junker's QuickXplain algorithms,
for explanation (finding minimal unsatisfiable subsets) and relaxation (maximal satisfiable subsets).
See [https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf](https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf).
This code can be used on stand-alone basis, plugging in any monotonic `check` or `assert` predicate.
For this Z3 integration, we use `z3_push`.
See [quickexplain.pl](https://github.com/turibe/swi-prolog-z3/blob/main/quickexplain.pl).

- Z3 can also explain inconsistency directly, with unsat cores. `z3_unsat_core(Formulas, Core)` gives a
subset of `Formulas` that is inconsistent with the formulas pushed so far (and fails if there is none);
Z3 keeps cores small, but they need not be minimal. `z3_minimal_core(Formulas, Core)` makes the core
minimal with QuickXplain, which gives the same result as `qexplain(z3_push, Formulas, Core)`, much
faster when only a few of many formulas conflict:

```prolog
?- z3_push(x:int > 5), z3_unsat_core([x < 3, y:int = 1], Core).
Core = [x<3].
```

- `z3_explain(Formulas, Core)` and `z3_relax(Formulas, Kept)` run QuickXplain with Z3: `Core` is a
minimal subset of `Formulas` that conflict (with the formulas pushed so far), and `Kept` a maximal
subset that can all hold, preferring earlier formulas, so list the most important first. Use these
rather than `qexplain(z3_push, ...)` and `qrelax(z3_push, ...)`: QuickXplain pushes formulas one at a
time, and a formula pushed alone can get other types than with the rest (in `f(a) = f(b)`, `a` has no
numeric type yet, so a later `a = 1` is a type error), which `z3_push` reports by failing, as it does a
conflict. `z3_explain` and `z3_relax` type all the formulas together first. `z3_minimal_core(Formulas,
Core)` is `z3_unsat_core` followed by `z3_explain`. With quantifiers, their consistency checks of
subsets may each take until the timeout, while `z3_unsat_core/2` stays fast.

[examples/explanations.pl](examples/explanations.pl) has worked examples: scheduling a meeting and
configuring a car within a budget, explained, relaxed and optimized, and a quick unsat core. Run it with
`./examples/explanations.pl`.

At the lower level, `z3_check_assumptions(Handle, Literals, Status)` checks under Boolean assumptions,
and `z3_get_unsat_core(Handle, Core)` gives the ones an `l_false` result used.

## Documentation

From swipl, run
```prolog
?- doc_server(8080).
```
and navigate to [http://localhost:8080/pldoc/](http://localhost:8080/pldoc/) to see docs.

## Future Work

- The current version handles the following Z3 capabilities:
{int,real,bool} types, propositional logic, equality, arithmetic, bit vectors, and uninterpreted function symbols.
Other Z3 features such as arrays, sets and quantifiers are future work.

- Big integers and rationals could be passed between Prolog and Z3 using [GMP](https://gmplib.org/),
the arbitrary-precision library SWI-Prolog uses for them, instead of going through text.
Currently, an integer that does not fit in 64 bits is converted to a decimal string and given to `Z3_mk_numeral`,
a Prolog rational is split into numerator and denominator with `rational/3`,
and large numbers coming back from Z3 are parsed from Z3's string form.
With GMP, the C code could read them directly with `PL_get_mpz`/`PL_get_mpq` and build terms with `PL_unify_mpz`/`PL_unify_mpq`.
This would avoid the string round trips, though Z3's C API itself takes numerals as strings,
so the gain would mostly be on the way back to Prolog.
It would also add a build dependency on GMP: its headers on the include path
(for Homebrew, `-I/opt/homebrew/include`) and `-lgmp` when linking.
There is commented-out code for this in `z3_swi_foreign.c`.


