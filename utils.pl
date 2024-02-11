%%% -*- Mode: Prolog; Module: utils; -*-

:- module(utils, [
	      split_list/3,
	      subterm_list/2
    ] ).


% split list in half:
split_list(L, A, B) :- length(L, N),
    Half is N div 2,
    Rest is N - Half,
    length(A, Half),
    length(B, Rest),
    append(A, B, L).


subterm_list(T, L) :- findall(Y, arg(_, T, Y), L).



:- begin_tests(util_tests).

test(empty) :-
    split_list([], [], []).

test(one) :-
    split_list([a], [], [a]).

test(odd) :-
    split_list([a,b,c,d,e], [a,b], [c,d,e]).

test(even, true(X == [3,4])) :-
    split_list([1,2,3,4], [1,2], X).


:- end_tests(util_tests).
