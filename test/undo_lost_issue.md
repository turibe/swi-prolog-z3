**Title:** `undo/1` goal never runs under plunit (a test with `true(...)` after exactly two tests)

**Description**

A goal registered with `undo/1` is sometimes never run. In the example below, a plunit test schedules two undo goals, but when the test ends only one of them runs. The other doesn't run later either. The example uses only the standard library.

**To reproduce**

`undo_lost.pl`:

```prolog
u(X) :- format(user_error, "UNDO ~w~n", [X]).

two :-
    undo(u(first)),
    undo(u(second)).

:- begin_tests(undo_lost).

test(x) :- true.
test(y) :- true.
test(c, [true(X == 1)]) :- two, X = 1.

:- end_tests(undo_lost).
```

```
$ swipl -g run_tests -t halt undo_lost.pl
```

**Expected:** after test `c`, both `UNDO second` and `UNDO first` are printed.

**Actual:**

```
% Start unit: undo_lost
% [1/3] undo_lost:x ................................. passed (0.003 sec)
% [2/3] undo_lost:y ................................. passed (0.000 sec)
% [3/3] undo_lost:c ................................. passed (0.000 sec)
UNDO second
% End unit undo_lost: passed (0.005 sec CPU)
% All 3 tests passed in 0.009 seconds (0.007 cpu)
```

`UNDO first` is never printed. This happens on every run.

**When it happens**

Changing any one of these makes both undo goals run:
- one or three tests before `c`, instead of two (the earlier tests can be trivial, like `test(x) :- true.`);
- no `true(...)` option on `c`, as in `test(c) :- two.`;
- `c` as the first test.

I couldn't reproduce it outside plunit. I tried calling `two` under the same control constructs plunit uses for a `true(...)` test: `call_cleanup/2` inside `catch/3` inside an if-then-else, followed by backtracking. Every combination I tried ran both goals.

**Why it matters**

I'm using `undo/1` to make a foreign solver's state follow backtracking. Each push of a formula registers its pop, plus the removal of the symbols it declared. Losing one of these leaves stale state behind, and in my test suite it made later tests fail.

**Environment**

- SWI-Prolog 11.0.0 for arm64-darwin (Homebrew bottle)
- macOS 15 (Darwin 24.6.0), Apple silicon
