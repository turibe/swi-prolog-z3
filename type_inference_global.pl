%%% -*- Mode: Prolog; Module: z3; -*-
    
:- module(type_inference_global, [
              show_map/1,
              assert_formula_list_types/1,
              assert_type/2,
              get_map/1,
              show_map/1
          ]).

:- use_module(library(assoc)).

%%%%%%%%%%%%%%%%%%%%
%%
%% This module builds on type_inference.pl and keeps a global backtrackable type map so we can incrementally typecheck in the REPL.
%%
%% Note also that we keep a mirror of this state in the C package for Z3 as well, that can be reset between queries.
%%

:- use_module(type_inference).

:- initialization(initialize_map).

%% NEW: we use a backtrackable version.
%% TODO: Would be nice, for efficiency, to only get the deltas from one type map to the next, and assert only those.

initialize_map :- empty_assoc(Empty),
		  initialize_map(Empty).

initialize_map(Map) :- nb_setval(global_typemap, Map).

get_map(Map) :- b_getval(global_typemap, Map).
    
set_map(Map) :- b_setval(global_typemap, Map).

show_map(L) :- get_map(Map),
               assoc_to_list(Map, L).

%% gets the current map, uses it to typecheck the formula list, and updates the current map with the result:
assert_formula_list_types(L) :-
    get_map(E),
    typecheck_formula_list(L, E, Enew),
    set_map(Enew).


assert_type(Term, Type) :- ground(Term),
                           get_map(E),
                           typecheck(Term, Type, E, Enew),
                           set_map(Enew).
assert_type(Term, _Type) :- \+ ground(Term),
                            instantiation_error(Term).


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
