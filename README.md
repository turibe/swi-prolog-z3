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
allocated from `z3_swi_foreign.so`. Set `LEAK_ITERATIONS` to change the workload size (default 2000).
It finds memory that is never freed, not objects that are kept alive longer than needed but are freed
with their handle.

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

Using `z3.pl`, all assertions and type declarations (except for enums) are reset from one query to the next.
The stateful_repl module offers an alternative to `z3.pl`, where assertions and declarations are accumulated,
similarly to the Python integration or the Z3 prompt.

The main queries / commands are:
- add(+Formula)
- asserted(-FormulaList)
- reset
- is_implied(+Formula)
- is_consistent(+Formula)
- model(-Model)
- declarations(-Declarations)

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
  - `isoneof/N` and `alldifferent/N`, macros (see above).
- Constants: `true`, `false`.
- Sort names, in `Term:Sort` and declarations: `int` or `integer`, `real`, `float` or `double`
  (all three are Z3's reals), `bool` or `boolean`, `bv(N)`, `string`, and the names of declared enumeration sorts.
  Any other atom names an uninterpreted sort.
- Logic: `and`, `or`, `not`, `implies`, `iff`, `xor`, `ite`, and the operators `,`, `;`, `->`, `<=>`.
- Equality and comparison: `=`, `==`, `equal`, `equals`, `<>`, `distinct`, `<`, `>`, `=<`, `>=`,
  `leq`, `geq`, `between`.
- Arithmetic: `+`, `-`, `minus`, `*`, `/`, `div`, `mod`, `rem`, `divides`, `power`, `**`, `^`,
  `is_int`, `int2real`, `real2int`.
- Pseudo-Boolean: `atleast`, `atmost`.
- Strings, with arguments in the SMT-LIB order: `str_concat/N`, `str_len/1`, `str_substr/3` (string, offset,
  length), `str_at/2` (the one-character string at an index), `str_contains/2` (container, containee),
  `str_prefixof/2` and `str_suffixof/2` (prefix or suffix first), `str_indexof/3` (string, substring, start;
  -1 if absent), `str_replace/3` (the first occurrence), `str_lt/2` and `str_le/2` (lexicographic),
  `str_to_int/1` (-1 unless all digits), `int_to_str/1` ("" for negative numbers).
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


