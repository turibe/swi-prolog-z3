# Examples

Worked examples of using Z3 from SWI-Prolog. Most of them are short questions with Z3's answers, one
file per feature, using the high-level API in [`z3.pl`](../z3.pl).

## Before you start

Build the library first, from the repository root (see the main [README](../README.md) for installing
SWI-Prolog and Z3):

```bash
make
```

## Running an example

Each file is an executable script that prints its questions and answers. Run it from any directory:

```bash
./examples/strings.pl
```

or with `swipl` explicitly:

```bash
swipl examples/strings.pl
```

The output looks like this:

```
Find a password of 8 characters that starts with Z, ends with !, contains a 7, and has no spaces.
  "Z7ABCDE!"

Which 4-character string x makes x ++ "ab" equal to "ab" ++ x?
  "abab"
...
```

## Exploring interactively

Loading a file does not run it, so you can run one example at a time, or look at the code behind an
answer. Start `swipl` in the repository root:

```prolog
?- use_module(examples/strings).
?- example(password).                 % prints the question and the answer
?- example(password, Answer).         % just the answer, as a Prolog term
?- example(Name).                     % all of them, one at a time on backtracking
```

Each file is a module, and every example is a `question/2` and `answer/2` pair, so a new question is easy
to add next to the others.

## Running the tests

Each file has unit tests of its answers. Run them by name (the names are in the table below):

```bash
swipl -g "run_tests(string_examples)" -t halt examples/strings.pl
```

or, from inside `swipl`, after loading the file:

```prolog
?- run_tests(string_examples).
```

Name the unit: `run_tests` with no argument also runs the library's own tests, which every example
loads. To run the tests of all the examples:

```bash
for e in strings:string_examples arrays:array_examples algebraic_numbers:algebraic_examples \
         floating_point:floating_point_examples optimization:optimization_examples \
         quantifiers:quantifier_examples explanations:explanation_examples \
         timeouts:timeout_examples einstein:einstein; do
  swipl -g "run_tests(${e#*:})" -t halt "examples/${e%%:*}.pl"
done
```

(`make test` runs the library's own tests, not these.)

## The examples

| File | What it shows | Tests | Time |
|---|---|---|---|
| [`strings.pl`](strings.pl) | Solving for strings: a password, a word equation, splitting an email address, digits, Unicode, lexicographic order | `string_examples` | 0.4 s |
| [`arrays.pl`](arrays.pl) | Finding arrays, swapping elements, which stores commute, a lookup table, a matrix as an array of arrays | `array_examples` | 0.3 s |
| [`algebraic_numbers.pl`](algebraic_numbers.pl) | Irrational solutions, given exactly: the golden ratio, square and cube roots, a root that cannot be written with radicals | `algebraic_examples` | 0.2 s |
| [`floating_point.pl`](floating_point.pl) | IEEE floating point: `0.1 + 0.2`, NaN, rounding modes, associativity, summation order, an overflowing midpoint, `sqrt(x * x)` | `floating_point_examples` | 3 s |
| [`optimization.pl`](optimization.pl) | A production plan, a knapsack, lexicographic priorities, weighted preferences, unbounded objectives | `optimization_examples` | 0.3 s |
| [`quantifiers.pl`](quantifiers.pl) | `forall` and `exists`: a syllogism, properties of functions and arrays, a definition by an axiom, a question Z3 cannot settle | `quantifier_examples` | 1 s |
| [`explanations.pl`](explanations.pl) | Explaining and relaxing conflicts (`z3_explain`, `z3_relax`, unsat cores): scheduling a meeting, configuring a car within a budget | `explanation_examples` | 0.4 s |
| [`timeouts.pl`](timeouts.pl) | Stopping a long check: a timeout, `call_with_time_limit/2`, `z3_interrupt/1` from another thread | `timeout_examples` | 2 s |
| [`einstein.pl`](einstein.pl) | The Einstein (zebra) puzzle, with enumeration sorts. Also `make einstein` | `einstein` | 0.4 s |
| [`pigeonhole.pl`](pigeonhole.pl) | The pigeonhole problem with the low-level `z3_swi_foreign` API, timed for increasing sizes | — | 1.5 s |

Two of them take arguments or work differently:

- `pigeonhole.pl` takes the largest size to try, 9 by default; each size takes roughly twice as long as
  the one before:

  ```bash
  ./examples/pigeonhole.pl 6
  ```

- [`test_explain_clp.pl`](test_explain_clp.pl) uses QuickXplain with SWI-Prolog's CLP(FD) and CLP(R)
  libraries rather than Z3. It is not a script: load it from the repository root and call its
  predicates:

  ```bash
  swipl examples/test_explain_clp.pl
  ```
  ```prolog
  ?- test2(R).
  R = [{_A>_B}].
  ```
