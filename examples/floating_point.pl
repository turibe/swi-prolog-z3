#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: floating_point_examples; -*-

%% Examples of IEEE floating point: what computer arithmetic actually does, as opposed to the reals.
%% Sorts are float16, float32, float64, float128, or fp(Ebits, Sbits). Operations take a rounding mode
%% first, as in SMT-LIB: fp_add(rne, X, Y) adds, rounding to nearest (ties to even); rtp, rtn and rtz
%% round toward positive or negative infinity or toward zero. Constants are fp_value(Value, Sort),
%% with Value a number, nan, inf or -inf, and models give values in the same form.
%%
%% fp_eq/2 is IEEE equality, as in C's ==: NaN is not equal to itself. = is identity: NaN = NaN, and
%% 0.0 and -0.0 are different. +, < and so on are for int and real; use fp_add, fp_lt, and so on.
%%
%% Some questions use float16, which has the same pitfalls as float32 and float64 but lets Z3 answer
%% faster: it decides floating-point questions by reasoning about their bits.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/floating_point.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/floating_point).
%%     ?- example(point_three).
%%     ?- run_tests(floating_point_examples).

:- module(floating_point_examples, [
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
    format("~w~n  ~W~n~n", [Question, Answer, [module(floating_point_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

% The values of the constants Names in a model of the formulas pushed so far.
values(Names, Values) :-
    z3_model(M),
    maplist([N, V]>>memberchk(N = V, M.constants), Names, Values).

question(point_three,
         "In double precision, is 0.1 + 0.2 equal to 0.3?").
question(not_equal_to_itself,
         "Is there a float32 x for which x == x is false?").
question(plus_one,
         "What is the smallest positive float32 x for which x + 1 == x?").
question(rounding,
         "What is 1/3 as a float32, rounded down and rounded up?").
question(associativity,
         "Is floating-point addition associative? Find a, b and c with (a + b) + c != a + (b + c).").
question(summation_order,
         "Does the order of a sum of positive numbers matter? Find a, b and c with (a + b) + c != (c + b) + a.").
question(midpoint_overflow,
         "Can the midpoint (a + b) / 2 of two finite numbers be infinite?").
question(midpoint_fixes,
         "Which of a + (b - a) / 2 and a / 2 + b / 2 never overflows, for finite a and b?").
question(square_root,
         "Is sqrt(x * x) = x for every positive x?").

% The sum is the double nearest to 0.1 + 0.2 as rounded, which is not the double nearest to 0.3.
answer(point_three, sum(Sum)-equal_to_point_three(Equal)) :-
    z3_push(s:float64 = fp_add(rne, fp_value(0.1, float64), fp_value(0.2, float64))),
    values([s], [fp_value(Sum, float64)]),
    ( z3_is_implied(fp_eq(s, fp_value(0.3, float64))) -> Equal = yes ; Equal = no ).

% NaN, the result of 0/0 or sqrt(-1), is the only value that is not equal to itself.
answer(not_equal_to_itself, X) :-
    z3_push(not(fp_eq(x:float32, x))),
    values([x], [X]).

% A float32 has 24 bits of precision, so above 2^24 = 16777216 the gap between neighbors is 2 or more,
% and adding 1 rounds back. Z3 proves no smaller x works, and that 2^24 does.
answer(plus_one, smallest(Smallest)) :-
    Big = fp_value(16777216, float32),
    z3_push(fp_is_positive(x:float32) and not(fp_is_infinite(x))),
    z3_push(fp_eq(fp_add(rne, x, fp_value(1, float32)), x)),
    z3_is_implied(fp_geq(x, Big)),
    z3_reset,
    z3_is_implied(fp_eq(fp_add(rne, Big, fp_value(1, float32)), Big)),
    Big = fp_value(Smallest, _).

answer(rounding, down(Down)-up(Up)) :-
    z3_push(down:float32 = fp_div(rtn, fp_value(1, float32), fp_value(3, float32))),
    z3_push(up:float32 = fp_div(rtp, fp_value(1, float32), fp_value(3, float32))),
    values([down, up], [fp_value(Down, _), fp_value(Up, _)]).

% Each addition rounds, so grouping changes which roundings happen.
answer(associativity, [a = A, b = B, c = C]) :-
    z3_push(fp_is_normal(a:float16) and fp_is_normal(b:float16) and fp_is_normal(c:float16)),
    z3_push(not(fp_eq(fp_add(rne, fp_add(rne, a, b), c), fp_add(rne, a, fp_add(rne, b, c))))),
    values([a, b, c], [A, B, C]).

% Even with no cancellation, summing in a different order rounds differently.
answer(summation_order, [a = A, b = B, c = C]) :-
    z3_push(fp_is_normal(a:float16) and fp_is_positive(a) and fp_is_normal(b:float16) and fp_is_positive(b)
            and fp_is_normal(c:float16) and fp_is_positive(c)),
    z3_push(not(fp_eq(fp_add(rne, fp_add(rne, a, b), c), fp_add(rne, fp_add(rne, c, b), a)))),
    values([a, b, c], [A, B, C]).

% The sum a + b can overflow to infinity before the division brings it back in range.
answer(midpoint_overflow, [a = A, b = B]) :-
    finite_numbers([a:float16, b:float16]),
    z3_push(fp_is_infinite(fp_div(rne, fp_add(rne, a, b), fp_value(2, float16)))),
    values([a, b], [A, B]).

% b - a overflows too when a and b have opposite signs; halving first cannot overflow.
answer(midpoint_fixes, [a_plus_half_difference-First, half_plus_half-Second]) :-
    Two = fp_value(2, float16),
    never_infinite(fp_add(rne, a, fp_div(rne, fp_sub(rne, b, a), Two)), First),
    never_infinite(fp_add(rne, fp_div(rne, a, Two), fp_div(rne, b, Two)), Second).

% x * x can overflow to infinity, and the square root of infinity is infinity.
answer(square_root, counterexample(x = X)-square(Square)) :-
    z3_push(fp_is_normal(x:float16) and fp_is_positive(x)),
    z3_push(not(fp_eq(fp_sqrt(rne, fp_mul(rne, x, x)), x))),
    values([x], [X]),
    z3_reset,
    z3_push(sq:float16 = fp_mul(rne, X, X)),
    values([sq], [Square]).

% Not forall/2, which would undo the pushes: z3_push/1 is undone on backtracking.
finite_numbers(Vars) :-
    maplist([V]>>z3_push(not(fp_is_nan(V)) and not(fp_is_infinite(V))), Vars).

% Answer is safe if Term is never infinite for finite float16 numbers a and b, and unsafe if not.
never_infinite(Term, Answer) :-
    (   z3_is_implied(implies(not(fp_is_nan(a:float16)) and not(fp_is_infinite(a))
                              and not(fp_is_nan(b:float16)) and not(fp_is_infinite(b)),
                              not(fp_is_infinite(Term))))
    ->  Answer = safe
    ;   Answer = unsafe
    ).

:- begin_tests(floating_point_examples).

test(point_three) :-
    example(point_three, sum(Sum)-equal_to_point_three(Equal)),
    assertion(Sum =:= 0.1 + 0.2),                % Prolog's floats are doubles: the same sum
    assertion(Equal == no).

test(not_equal_to_itself) :-
    example(not_equal_to_itself, X),
    assertion(X == fp_value(nan, float32)).

test(plus_one) :-
    example(plus_one, smallest(S)),
    assertion(S =:= 2 ** 24).

test(rounding) :-
    example(rounding, down(Down)-up(Up)),
    assertion(Down < 1/3), assertion(Up > 1/3).

% The values found can be any that work; check that they do, by giving them back to Z3.
test(associativity) :-
    example(associativity, [a = A, b = B, c = C]),
    assertion(z3_is_implied(not(fp_eq(fp_add(rne, fp_add(rne, A, B), C), fp_add(rne, A, fp_add(rne, B, C)))))).

test(summation_order) :-
    example(summation_order, [a = A, b = B, c = C]),
    assertion(z3_is_implied(not(fp_eq(fp_add(rne, fp_add(rne, A, B), C), fp_add(rne, fp_add(rne, C, B), A))))).

test(midpoint_overflow) :-
    example(midpoint_overflow, [a = A, b = B]),
    assertion(z3_is_implied(not(fp_is_infinite(A)) and not(fp_is_infinite(B)))),
    assertion(z3_is_implied(fp_is_infinite(fp_div(rne, fp_add(rne, A, B), fp_value(2, float16))))).

test(midpoint_fixes) :-
    example(midpoint_fixes, Answer),
    assertion(Answer == [a_plus_half_difference-unsafe, half_plus_half-safe]).

test(square_root) :-
    example(square_root, counterexample(x = fp_value(X, float16))-square(Square)),
    assertion(X > 0),
    assertion(Square == fp_value(inf, float16)).

:- end_tests(floating_point_examples).
