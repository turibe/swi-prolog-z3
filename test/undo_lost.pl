% An undo/1 goal is lost (SWI-Prolog 11.0.0, arm64 macOS).
%
% two/0 schedules two undo goals, so each run should print both
% "UNDO first" and "UNDO second" when test c ends. It prints only
% "UNDO second": "UNDO first" is never run.
%
% It happens only with exactly two tests before c, and only when c has a
% true(...) option. One or three tests before it, no option on c, or c run
% first: both undo goals run.
%
% Run:  swipl -g run_tests -t halt test/undo_lost.pl
%
% Kept on the undo-solver branch, whose z3.pl relies on undo/1: there, a lost undo goal leaves a
% declaration or a solver scope behind, and 15 tests fail.

u(X) :- format(user_error, "UNDO ~w~n", [X]).

two :-
    undo(u(first)),
    undo(u(second)).

:- begin_tests(undo_lost).

test(x) :- true.
test(y) :- true.
test(c, [true(X == 1)]) :- two, X = 1.

:- end_tests(undo_lost).
