:- use_module(library(clpr)).
:- use_module(library(clpfd)).
:- use_module(library(clpb)).

:- use_module(quickexplain).    

doit(C1,C2,C3,C4) :-
    C1 in 1..10,
    C2 in 1..10,
    {X * C1 + Y * C2 = 10},
    {X * C3 + Y * C4 = 6},
    {X > Y},
    label([C1,C2]).

% insufficiently instantiated:
test1(R) :- qexplain(call, [ Y in 1..6, Z in 6..8, label([Y,Z]), {Y > Z}],R).
% idea: have Base include the "label" command, but do it last in the explain/relax algorithms.

test2(R) :- qexplain(call, [ Y in 1..5, Z in 6..8, label([Y,Z]), {Y > Z}],R).
