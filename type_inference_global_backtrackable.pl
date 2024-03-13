%%% -*- Mode: Prolog; Module: type_inference_global_backtrackable; -*-

:- module(type_inference_global_backtrackable, [
              initialize_map/0,
              initialize_map/1,
              assert_type/2,
              assert_formula_list_types/1,
              set_map/1,
              get_map/1,               % -Assoc : gets map as an assoc
              get_map_list/1           % gets map as a list
          ]).

/** <module> Global backtrackable type inference

This module builds on type_inference.pl and keeps a global backtrackable type map,
so we can incrementally typecheck formulas in the REPL.

Note that we keep a mirror of this state in the C Z3 package as well, needed to build terms.
Both sets of declarations can be inspected, as in decl/1 in stateful-repl.pl. 

@author Tomas Uribe
@license MIT
*/


:- use_module(library(assoc)).

:- use_module(type_inference).

:- initialization(initialize_map).

%% global_typemap is a backtrackable variable.

%! initialize_map(+AssocMap)
%  Initializes the global backtrackable variable.
initialize_map(Map) :- nb_setval(global_typemap, Map).

%! initialize_map
%  Initializes the global backtrackable variable to the empty assoc (`t`).
initialize_map :- empty_assoc(Empty),
		  initialize_map(Empty).

%! get_map(-Map)
%  Gets the map at the current backtracking point.
get_map(Map) :- b_getval(global_typemap, Map).
    
%! set_map(+Map)
%  Sets the map at the current backtracking point.
set_map(Map) :- b_setval(global_typemap, Map).

%! get_map_list(+List)
%  Gets the current map as a list (more readable than an assoc):
get_map_list(L) :- get_map(Map),
                   assoc_to_list(Map, L).

%! assert_formula_list_types(+FormulaList)
%  Gets the current type map, uses it to typecheck the formula list, and updates the current map with the result.
assert_formula_list_types(L) :-
    get_map(E),
    type_inference:typecheck_formula_list(L, E, Enew),
    set_map(Enew).


%! assert_type(+Term, +Type)
%  Type checks the given Term as having Type, and updates the current map accordingly.
assert_type(Term, Type) :- get_map(E),
                           type_inference:typecheck(Term, Type, E, Enew),
                           set_map(Enew).


%%%%%%%%%%%% unit tests %%%%%%%%%%%

:- begin_tests(type_inference_global, [setup(initialize_map)] ).

test(init) :-
    get_map(E), empty_assoc(E).

test(failtest, [fail]) :-
    assert_type(a, bool), assert_type(a, real).

test(inferencetest, [true(X-Y == int-lambda([int], int)) , nondet ]) :-
    assert_formula_list_types([f(a) > 1, b:int > a]),
    get_map(M),
    get_assoc(a/0, M, X),
    get_assoc(f/1, M, Y).


:- end_tests(type_inference_global).
