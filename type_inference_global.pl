%%% -*- Mode: Prolog; Module: z3; -*-

%%%%%%%%%%%%%%%%%%%%
%%
%% This module builds on type_inference.pl and keeps a global backtrackable type map so we can incrementally typecheck in the REPL.
%%
%% Note also that we keep a mirror of this state in the C Z3 package as well (needed to build terms), which should reset between queries.
%%

:- module(type_inference_global, [
              assert_type/2,
              declare_type_list/1,     % +List of Term-Type or Term:Type pairs
              typecheck_and_declare/2, % +Formula,-Assoc  : Typechecks Formula, declares types, and returns new Assoc
              get_map/1,               % -Assoc : gets map as an assoc
              get_map_list/1           % gets map as a list

          ]).

:- use_module(library(assoc)).

:- use_module(type_inference).

:- initialization(initialize_map).

%% global_typemap is a backtrackable variable.

initialize_map :- empty_assoc(Empty),
		  initialize_map(Empty).

initialize_map(Map) :- nb_setval(global_typemap, Map).

get_map(Map) :- b_getval(global_typemap, Map).
    
set_map(Map) :- b_setval(global_typemap, Map).

%% more readable:
get_map_list(L) :- get_map(Map),
                   assoc_to_list(Map, L).

%% gets the current map, uses it to typecheck the formula list, and updates the current map with the result:
assert_formula_list_types(L) :-
    get_map(E),
    type_inference:typecheck_formula_list(L, E, Enew),
    set_map(Enew).


assert_type(Term, Type) :- ground(Term), !,
                           get_map(E),
                           typecheck(Term, Type, E, Enew),
                           set_map(Enew).
assert_type(Term, _Type) :- \+ ground(Term),
                            instantiation_error(Term).

typecheck_and_declare(Formulas, Assoc) :-
    assert_formula_list_types(Formulas), !, %% updates the global (backtrackable) type map
    get_map(Assoc),
    assoc_to_list(Assoc, L),
    declare_type_list(L).


declare_type_list([]).
declare_type_list([A-B|R]) :- z3_declare(A, B), declare_type_list(R).
declare_type_list([A:B|R]) :- z3_declare(A, B), declare_type_list(R).


%%%%%%%%%%%% unit tests %%%%%%%%%%%

:- begin_tests(type_inference_global).

test(init) :-
    get_map(E), empty_assoc(E).

test(failtest, [fail]) :-
    assert_type(a, bool), assert_type(a, real).

test(inferencetest, [true(X-Y == int-lambda([int], int)) , nondet ]) :-
    assert_formula_list_types([f(a) > 1, b:int > a]),
    get_map(M),
    get_assoc(a, M, X),
    get_assoc(f/1, M, Y).


:- end_tests(type_inference_global).
