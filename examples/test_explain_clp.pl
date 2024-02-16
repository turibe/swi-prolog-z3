:- use_module(library(clpfd)).
% clpfd provides #=, #>, etc.

% :- use_module(library(clpq))
% provides {X = 5.0}

:- use_module(library(clpr)).
% provides {X = 5.0}

% :- use_module(library(clpb)).

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
% use a flag to control if base goes first or last? If we use pure constraints/predictates, it shouldn't matter.
% Use term_variables and add "labeling" automatically?
% (For non-clp, need it first; for clp, last.)

test2(R) :- qexplain(call, [ Y in 1..5, Z in 6..8, label([Y,Z])], [{Y > Z}],R).

test3(R) :- qrelax(call, [ Y in 1..5, Z in 6..8], [Y #> Z - 4, Y #= (Z - 1)],R).

% ERROR: '$clause_term_position'/3: Cannot represent due to `int'. Because of mixing?
% qrelax(call, [ Y in 1..5, Z in 6..8], [{Y > Z - 4.0}, {Y = (Z - 1.0)}],R).
