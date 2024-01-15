
:- module(type_inference_global, [
              reset_types/0,
              show_map/1,
              assert_formula_list_types/1,
              assert_type/2,
              get_type/2,
              get_map/1,
              show_map/1
          ]).

:- use_module(library(assoc)).

%%%%%%%%%%%%%%%%%%%%
%%
%% This module builds on type_inference.pl and keeps a global type map so we can incrementally typecheck in the REPL.
%%
%% This is ugly... Note also that we keep a mirror of this state in the C package for Z3 as well.
%%

:- use_module(type_inference).

:- initialization(reset_types).

%% NEW: we use a backtrackable version.
%% TODO: Would be nice, for efficiency, to only get the deltas from one type map to the next, and assert only those. But not critical.

reset_types :- print_message(information, format("reseting type inference map",[])),
    empty_assoc(Empty),
    initialize_map(Empty).

get_map(Map) :- b_getval(global_typemap, M),
                (M == [] -> empty_assoc(Map) ; Map = M).
set_map(Map) :- b_setval(global_typemap, Map).
initialize_map(Map) :- nb_setval(global_typemap, Map).

show_map(L) :- get_map(Map),
               assoc_to_list(Map, L).

%% gets the current map, uses it to typecheck the formula list, and updates the curent map with the result:
assert_formula_list_types(L) :-
    get_map(E),
    typecheck_formula_list(L, E, Enew),
    set_map(Enew).

assert_type(Term, Type) :- ground(Term), !,
                           get_map(E),
                           typecheck(Term, Type, E, Enew),
                           set_map(Enew).
assert_type(Term, _Type) :- type_error(ground, Term).

get_type(T, Type) :- get_map(E), typecheck(T, Type, E, _).
