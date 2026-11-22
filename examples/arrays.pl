#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: array_examples; -*-

%% Examples of arrays. Arrays have the sort array(IndexSort, ValueSort), and three operations:
%% select(A, I), the element at index I; store(A, I, V), A with the element at I set to V; and
%% const_array(IndexSort, V), the array with V everywhere. Arrays in Z3 have no length: every index
%% has an element. They are handy for modeling memory, tables and lookup functions, and for checking
%% what a sequence of updates does.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/arrays.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/arrays).
%%     ?- example(swap).
%%     ?- run_tests(array_examples).

:- module(array_examples, [
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
    format("~w~n  ~W~n~n", [Question, Answer, [module(array_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

question(find_array,
         "Find an array of integers with a[1] = 5 and a[2] = 7. What does Z3 give?").
question(swap,
         "Swapping a[0] and a[1] with two stores: does it swap them, and leave a[2] alone?").
question(commuting_stores,
         "Do two stores at different indices give the same array in either order?").
question(same_index_stores,
         "And two stores at the same index?").
question(lookup_table,
         "A table maps product codes to prices. If the total of products 1 and 2 is 30 and product 1 costs 12, what does product 2 cost?").
question(matrix,
         "A 2x2 matrix, as an array of rows: find one with 1s on the diagonal and 0s elsewhere.").

% Z3 gives an array as stores over a constant array: every element is the default, except those stored.
answer(find_array, A) :-
    z3_push(select(a:array(int, int), 1) = 5),
    z3_push(select(a, 2) = 7),
    z3_model(M),
    memberchk(a = A, M.constants).

answer(swap, Answer) :-
    z3_push(b:array(int, int) = store(store(a:array(int, int), 0, select(a, 1)), 1, select(a, 0))),
    ( z3_is_implied(select(b, 0) = select(a, 1) and select(b, 1) = select(a, 0) and select(b, 2) = select(a, 2))
    -> Answer = yes ; Answer = no ).

% Arrays are equal when all their elements are, so array equations can say "the same memory".
answer(commuting_stores, Answer) :-
    ( z3_is_implied(store(store(m:array(int, int), 1, 5), 2, 6) = store(store(m, 2, 6), 1, 5))
    -> Answer = yes ; Answer = no ).

% The later store wins, so the order matters.
answer(same_index_stores, Answer) :-
    ( z3_is_implied(store(store(m:array(int, int), 1, 5), 1, 6) = store(store(m, 1, 6), 1, 5))
    -> Answer = yes ; Answer = no ).

answer(lookup_table, price(2) = P) :-
    z3_push(select(price:array(int, int), 1) + select(price, 2) = 30),
    z3_push(select(price, 1) = 12),
    z3_push(p:int = select(price, 2)),
    z3_model(M),
    memberchk(p = P, M.constants).

answer(matrix, G) :-
    z3_push(select(select(g:array(int, array(int, int)), 0), 0) = 1),
    z3_push(select(select(g, 1), 1) = 1),
    z3_push(select(select(g, 0), 1) = 0),
    z3_push(select(select(g, 1), 0) = 0),
    z3_model(M),
    memberchk(g = G, M.constants).

:- begin_tests(array_examples).

expected(swap, yes).
expected(commuting_stores, yes).
expected(same_index_stores, no).
expected(lookup_table, price(2) = 18).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% The arrays can be any that meet the constraints; check that they do, by giving them back to Z3.
test(found_arrays_meet_constraints, [forall(member(Name-Check, [find_array-(select(a, 1) = 5 and select(a, 2) = 7),
                                                                 matrix-(select(select(g, 0), 0) = 1 and select(select(g, 1), 1) = 1
                                                                         and select(select(g, 0), 1) = 0 and select(select(g, 1), 0) = 0)]))]) :-
    example(Name, Value),
    ( Name == find_array -> Var = (a:array(int, int)) ; Var = (g:array(int, array(int, int))) ),
    z3_reset,
    z3_push(Var = Value),
    assertion(z3_is_implied(Check)).

:- end_tests(array_examples).
