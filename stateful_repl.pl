%%% -*- Mode: Prolog; Module: stateful_repl; --*

:- module(stateful_repl, [
              add/1,
              asserted/1, formulas/1,
              reset/0,
              declarations/1,
              model/1,
              scopes/1
              ]).

:- use_module(z3_swi_foreign, [
                  z3_make_solver/1,
                  z3_free_solver/1,
                  z3_reset_context/0,
                  z3_solver_push/2,
                  z3_assert/2,
                  z3_solver_check/2,
                  z3_model_map_for_solver/2,
                  z3_solver_pop/3,
                  z3_solver_scopes/2
              ]).

:- use_module(z3, [
                  declare_z3_types_for_symbols/2,
                  ground_version/3,
                  remove_type_annotations/2
              ]).

:- use_module(type_inference, [
                  typecheck/4
              ]).

:- use_module(library(assoc)).

% z3.pl shares no state between queries, except for enum declarations.

% this code, in contrast, shares everything: the solver, the type declarations, and the enums.

% can still pop the stack. Surgically remove assertions?
% also saves the session to disk to resume later

:- initialization(reset_globals).

get_global_solver(S) :- nb_current(global_solver, S).

get_type_map(M) :- nb_current(typecheck_map, M).
set_type_map(M) :- nb_setval(typecheck_map, M).

get_recorded_formulas(L) :- nb_current(recorded_formulas, L).
set_recorded_formulas(L) :- nb_setval(recorded_formulas, L).



record_formula(F) :- get_recorded_formulas(L),
                     append([[F], L], New),
                     set_recorded_formulas(New).

get_asserted(M) :- nb_current(asserted_formulas, M).

reset_globals :- (get_global_solver(S) -> z3_free_solver(S) ; true),
                 z3_reset_context, % to reset enums
                 z3_make_solver(NewSolver),
                 nb_setval(global_solver, NewSolver),
                 set_type_map(t),
                 set_recorded_formulas([]),
                 true.


add_formula(Formula) :-
    %% must_be(ground, Formula),
    get_type_map(OldAssoc),
    ground_version(Formula, FG, Symbols),
    typecheck(FG, bool, OldAssoc, NewMap), !, %% commit to first solution
    exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
    declare_z3_types_for_symbols(NewSymbols, NewMap),
    get_global_solver(Solver),
    z3_solver_push(Solver,_),
    remove_type_annotations(FG, FG_notypes),
    z3_assert(Solver, FG_notypes),
    z3_solver_check(Solver, Status), %% FIXME: do a pop if check fails
    (Status == l_false -> (z3_solver_pop(Solver, 1, _) , fail)
    ;
    (
        member(Status, [l_true, l_undef]), !,
        set_type_map(NewMap),
        record_formula(Formula)
    )
    ).

%% user-visible:

add(F) :- add_formula(F).
asserted(L) :- get_recorded_formulas(L).
formulas(L) :- get_recorded_formulas(L).
reset :- reset_globals.
declarations(L) :- get_type_map(M),
                   assoc_to_list(M, L).

model(Model) :- get_global_solver(S),
                z3_model_map_for_solver(S, Model).

scopes(N) :- get_global_solver(S),
             z3_solver_scopes(S, N).

/** TODO: need a local "push" operation that doesn't change global variables.
is_implied(F) :- get_global_solver(S),
                 z3_solver_push(S, not(F)),
                 z3_solver_check(S, Status),
                 (Status == l_true -> (z3_solver_pop(S), fail)
                 ;
                 (Status == l_undef -> (z3_solver_pop(S), fail)
                 ;
                 (Status == l_type_error -> fail
                 ;
                 (
                     popn(1)
                 ))));
*/
    
/****
%% give option to pop last asserted thing? But types remain...
z3_pop(Formula) :-
    must_be(var, Formula),
    pop_recorded_formulas(Formula),
    get_global_solver(S),
    z3_solver_pop(S).               
****/
