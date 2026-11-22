#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: algebraic_examples; -*-

%% Examples of irrational solutions. With nonlinear real arithmetic, a solution can be irrational, like
%% the square root of 2. Z3 represents it exactly, and z3.pl gives it as
%%
%%     algebraic(Approx, root(Coefficients, Index))
%%
%% where Approx is a float close to the value, and the exact value is the Index-th smallest real root
%% of the polynomial with integer Coefficients, lowest degree first: root([-2, 0, 1], 2) is the larger
%% root of x^2 - 2, the positive square root of 2. Such terms can be used in formulas again, where
%% they mean the exact value (Approx is then ignored).
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/algebraic_numbers.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/algebraic_numbers).
%%     ?- example(golden_ratio).
%%     ?- run_tests(algebraic_examples).

:- module(algebraic_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').

:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

example(Name, Answer) :- question(Name, _), z3_reset, answer(Name, Answer).

example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(algebraic_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

% The value of the constant Name in a model of the formulas pushed so far.
value(Name, Value) :- z3_model(M), memberchk(Name = Value, M.constants).

question(golden_ratio,
         "The golden ratio is the positive x with x * x = x + 1. What does Z3 give for it?").
question(exact_check,
         "Is the value Z3 gave exactly the golden ratio: does it satisfy x * x = x + 1 exactly?").
question(cube_root,
         "What is the real cube root of 2?").
question(diagonal,
         "How long is the diagonal of a square with sides of length 1?").
question(float_check,
         "The diagonal of a unit square is the square root of 2. Does its float approximation square to exactly 2?").
question(no_radicals,
         "What is the real solution of x^5 = x + 1? (It cannot be written with roots.)").

% x^2 - x - 1 = 0, lowest degree first: [-1, -1, 1]; the positive root is the larger one, index 2.
answer(golden_ratio, X) :-
    z3_push(x:real * x = x + 1.0 and x > 0.0),
    value(x, X).

% The exact value can be pushed back, and keeps its meaning.
answer(exact_check, Answer) :-
    answer(golden_ratio, Phi),
    z3_reset,
    z3_push(y:real = Phi),
    ( z3_is_implied(y * y = y + 1.0) -> Answer = yes ; Answer = no ).

% Floats are approximations: the float closest to the square root of 2 squares to slightly more
% than 2, while the exact value Z3 gives squares to exactly 2 (see exact_check for the same idea).
answer(float_check, Answer-squares_to(Square)) :-
    answer(diagonal, algebraic(Approx, _)),
    Square is Approx * Approx,
    ( Square =:= 2 -> Answer = yes ; Answer = no ).

answer(cube_root, X) :-
    z3_push(x:real * x * x = 2.0),
    value(x, X).

answer(diagonal, D) :-
    z3_push(d:real * d = 1.0 * 1.0 + 1.0 * 1.0 and d > 0.0),
    value(d, D).

answer(no_radicals, X) :-
    z3_push(x:real * x * x * x * x = x + 1.0),
    value(x, X).

:- begin_tests(algebraic_examples).

expected(golden_ratio, algebraic(_, root([-1, -1, 1], 2))).
expected(exact_check, yes).
expected(float_check, no-squares_to(_)).
expected(cube_root, algebraic(_, root([-2, 0, 0, 1], 1))).
expected(diagonal, algebraic(_, root([-2, 0, 1], 2))).
expected(no_radicals, algebraic(_, root([-1, -1, 0, 0, 0, 1], 1))).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(subsumes_term(Expected, Answer)).

test(approximations, [forall(member(Name-Exact, [golden_ratio-((1 + sqrt(5)) / 2), cube_root-(2 ** (1/3)),
                                                  diagonal-sqrt(2)]))]) :-
    example(Name, algebraic(Approx, _)),
    assertion(abs(Approx - Exact) < 1.0e-15).

:- end_tests(algebraic_examples).
