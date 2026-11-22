#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: optimization_examples; -*-

%% Examples of optimization. z3_optimize(Objectives, Model) finds a model of the formulas pushed so
%% far that is best for Objectives, a list in priority order of
%%
%%     minimize(T), maximize(T)     an arithmetic (or bit-vector) term T
%%     soft(F), soft(F, Weight)     a formula F that should hold if possible, worth Weight (default 1)
%%
%% All the soft constraints together count as one objective: violating as little weight as possible.
%% The model has an extra key, objectives, with each objective's value.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/optimization.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/optimization).
%%     ?- example(production).
%%     ?- run_tests(optimization_examples).

:- module(optimization_examples, [
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
    format("~w~n  ~W~n~n", [Question, Answer, [module(optimization_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

question(production,
         "A workshop makes chairs (profit 30) and tables (profit 50). A chair takes 2 hours of carpentry and 1 of finishing; a table 3 of each. With 120 hours of carpentry and 90 of finishing, what should it make?").
question(knapsack,
         "A backpack holds 8 kg. Map (2 kg, worth 3), tent (5 kg, worth 8), stove (3 kg, worth 4), book (1 kg, worth 1): what should go in?").
question(priorities,
         "With x + y at most 10, maximize x first and then y, or y first and then x: what do we get?").
question(preferences,
         "Three friends choose a restaurant: Ana prefers Thai (weight 3), Ben prefers pizza (weight 2), Cy anything but Thai (weight 2). Which one?").
question(unbounded,
         "Over the integers with x > 0, what is the largest x? And over the reals, the smallest x > 0?").

answer(production, plan(Plan)-profit(Profit)) :-
    z3_push(chairs:int >= 0 and tables:int >= 0),
    z3_push(2 * chairs + 3 * tables =< 120),                % carpentry hours
    z3_push(chairs + 3 * tables =< 90),                     % finishing hours
    z3_optimize([maximize(30 * chairs + 50 * tables)], M),
    Plan = M.constants,
    M.objectives = [_ = Profit].

% Booleans count as 0 or 1 in arithmetic, so the weight is a sum over the items taken. The items
% are annotated as bool in the sum: there, nothing else says they are not integers.
answer(knapsack, take(Taken)-value(Value)) :-
    Items = [map-(2-3), tent-(5-8), stove-(3-4), book-(1-1)],
    foldl([I-(W-_), S, S + W * (I:bool)]>>true, Items, 0, Weight),
    z3_push(Weight =< 8),
    findall(soft(I, V), member(I-(_-V), Items), Soft),
    z3_optimize(Soft, M),
    findall(I, (member(I-_, Items), memberchk(I = true, M.constants)), Taken),
    foldl([I, S0, S]>>(memberchk(I-(_-V), Items), S is S0 + V), Taken, 0, Value).

% Objectives are lexicographic: the first is optimized first, and the next only among its optima.
answer(priorities, [x_first-XFirst, y_first-YFirst]) :-
    z3_push(x:int >= 0 and y:int >= 0 and x + y =< 10),
    z3_optimize([maximize(x), maximize(y)], M1), XFirst = M1.constants,
    z3_optimize([maximize(y), maximize(x)], M2), YFirst = M2.constants.

% Exactly one restaurant; each preference is a soft constraint with a weight.
answer(preferences, Choice) :-
    z3_push(atleast(thai:bool, pizza:bool, sushi:bool, 1) and atmost(thai, pizza, sushi, 1)),
    z3_optimize([soft(thai, 3), soft(pizza, 2), soft(not(thai), 2)], M),
    member(Choice, [thai, pizza, sushi]),
    memberchk(Choice = true, M.constants), !.

% When there is no optimum, the value says so: oo is infinity, and epsilon an infinitesimal (the
% smallest real above 0 does not exist, but the values approach 0 + epsilon).
answer(unbounded, [largest_integer-Largest, smallest_positive_real-Smallest]) :-
    z3_push(x:int > 0),
    z3_optimize([maximize(x)], M1), M1.objectives = [_ = Largest],
    z3_reset,
    z3_push(r:real > 0.0),
    z3_optimize([minimize(r)], M2), M2.objectives = [_ = Smallest].

:- begin_tests(optimization_examples).

expected(production, plan([chairs = 30, tables = 20])-profit(1900)).
expected(priorities, [x_first-[x = 10, y = 0], y_first-[x = 0, y = 10]]).
expected(preferences, pizza).
expected(unbounded, [largest_integer-oo, smallest_positive_real-epsilon]).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% Two choices are worth 12 (map, tent and book, or tent and stove); either is optimal.
test(knapsack) :-
    example(knapsack, take(Taken)-value(Value)),
    assertion(Value == 12),
    assertion(memberchk(Taken, [[map, tent, book], [tent, stove]])).

:- end_tests(optimization_examples).
