%%% -*- Mode: Prolog; Module: stateful_repl; -*-.


:- module(stateful_repl, [
              add/1,
              asserted/1, formulas/1,
              reset/0,
              declarations/1,
              model/1,
              scopes/1,
              decl/1,
              implies/1,
              is_implied/1,
              is_consistent/1,

              save_state/1,
              read_state/1,

              z3_help/0,

              % can this repetition be avoided?
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>),  % different-than
              op(739, xfy, <=>), % iff
              op(199, xfy, :)

          ]).
    
/** <module> Stateful REPL for Z3

Remembers asserted formulas and declarations from one query to the next.

*/

:- use_module(z3_swi_foreign, [
                  z3_make_solver/1,
                  z3_free_solver/1,
                  z3_reset_context/0,
                  z3_solver_push/2,
                  z3_assert/2,
                  z3_solver_check/2,
                  z3_model_map_for_solver/2,
                  z3_solver_pop/3,
                  z3_solver_scopes/2,
                  z3_declarations/1,
                  z3_remove_declaration/2,
                  z3_current_context_id/1
              ]).

:- use_module(z3_utils, [
                  declare_z3_types_for_symbols/2,
                  ground_version/3,
                  remove_type_annotations/2
              ]).

:- use_module(type_inference, [
                  typecheck/4
              ]).

:- use_module(library(assoc)).

% TODO: allow adding inconsistencies, add explain/relax?


z3_help :- writeln("Z3 repl help\n"),
           writeln("add(F)\t\tAdd formula F"),
           writeln("reset\t\tReset all declarations"),
           true.

% z3.pl shares no state between queries, except for enum declarations.

% this code, in contrast, shares everything: the solver, the type declarations, and the enums.

% can still pop the stack. Surgically remove assertions?
% also saves the session to disk to resume later

:- initialization(reset_globals).

% fails if the variable does not exist:
get_repl_solver(S) :- nb_current(repl_solver, (_, S)).
get_type_map(M) :- nb_current(typecheck_map, M).
set_type_map(M) :- nb_setval(typecheck_map, M).

get_recorded_formulas(L) :- nb_current(recorded_formulas, L).
set_recorded_formulas(L) :- nb_setval(recorded_formulas, L).

record_formula(F) :- get_recorded_formulas(L),
                     append([[F], L], New),
                     set_recorded_formulas(New).

get_asserted(M) :- nb_current(asserted_formulas, M).

% we should call reset_globals if there is a chance for the context to be invalidated
% before we do a reset. Otherwise, we'll have an old invalid pointer as the solver.

clear_solver :- nb_current(repl_solver, (Context, S)), !,
                z3_current_context_id(CurrentContext),
                (CurrentContext = Context
                ->
                    (
                        z3_solver_scopes(S, N),
                        z3_solver_pop(S, N, X),
                        writef("Scopes was %w", [N]),
                        assertion(X == 0),
                        z3_free_solver(S)
                    )
                ; writef("There's a new context, previous solver is invalidated.")
                ),
                nb_delete(repl_solver).
clear_solver :- true.


reset_globals :- clear_solver,
                 z3_reset_context, % resets everything, including enums
                 z3_current_context_id(Context),
                 z3_make_solver(NewSolver),
                 nb_setval(repl_solver, (Context, NewSolver)),
                 set_type_map(t),
                 set_recorded_formulas([]),
                 true.

push_formula(Formula, NewMap, NewSymbols, Status) :-
    %% must_be(ground, Formula),
    get_type_map(OldAssoc),
    ground_version(Formula, FG, Symbols),
    (typecheck(FG, bool, OldAssoc, NewMap) -> true ;
     writef("Type error for %w", [FG]),
     fail
     ),
    !, %% commit to first solution
    exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
    declare_z3_types_for_symbols(NewSymbols, NewMap),
    get_repl_solver(Solver),
    z3_solver_push(Solver, _),
    remove_type_annotations(FG, FG_notypes),
    z3_assert(Solver, FG_notypes),
    z3_solver_check(Solver, Status).



remove_one(F/N) :- z3_remove_declaration(F, N).
remove_declarations(L) :- maplist(remove_one, L). % all declarations should have the form F/N

%! add_formula(+F)
%  Adds Z3 formula F. Typechecks and adds resulting declarations as well.
add_formula(F) :- push_formula(F, NewMap, NewSymbols, Status),
                  (member(Status, [l_false, l_type_error])  -> (
                                           get_repl_solver(Solver),
                                           z3_solver_pop(Solver, 1, _),
                                           remove_declarations(NewSymbols),
                                           fail
                                        )
                  ; (
                      set_type_map(NewMap),
                      record_formula(F)
                  )).

%! decl(-M)
%  Get all declarations
decl(M) :-
    z3_declarations(Z),
    declarations(D),
    M = {z3:Z, pl:D}.
    
%% user-visible:

%! add(+F)
%  Shortcut for add_formula
add(F) :- add_formula(F).

%! asserted(-List)
%  Get list of asserted formulas.
asserted(L) :- get_recorded_formulas(L).
formulas(L) :- get_recorded_formulas(L).

%! reset
%  Clear all formulas and declarations.
reset :- reset_globals.

%! declarations(-L)
%  Get declarations, both at the Prolog and Z3 levels.
declarations(L) :- get_type_map(M),
                   assoc_to_list(M, L).

%! model(-Model)
%  Get a Z3 model of formulas asserted so far.
model(Model) :- get_repl_solver(S),
                z3_model_map_for_solver(S, Model).

scopes(N) :- get_repl_solver(S),
             z3_solver_scopes(S, N).

push_check_and_pop(F, Status) :-
    push_formula(F, _NewMap, NewSymbols, Status),
    get_repl_solver(Solver),
    z3_solver_pop(Solver, 1, _),
    remove_declarations(NewSymbols).

is_implied(F) :- push_check_and_pop(not(F), Status),
                 Status == l_false.

%% todo: handle l_undef
is_consistent(F) :- push_check_and_pop(F, Status),
                    Status == l_true.
    

implies(X) :- is_implied(X).
    
/****
%% give option to pop last asserted thing? But types remain...
%% Could include in the stack the new tupes introduced at each step, erase them on pop.
z3_pop(Formula) :-
    must_be(var, Formula),
    pop_recorded_formulas(Formula),
    get_repl_solver(S),
    z3_solver_pop(S).               
****/

save_state(Filename) :-
    open(Filename, write, Output, [create([all])] ),
    formulas(L),
    write_canonical(Output, L), %% fast_write fails?
    writeln(Output, "."),
    close(Output).

read_state(Filename) :-
    open(Filename, read, Input),
    read(Input, L),
    close(Input),
    maplist(add, L).

:- begin_tests(repl_tests,
               [setup(reset), cleanup(reset)]
              ).

test(instantiate_type) :-
    reset,
    add(a:bv(32) = b:bv(X)),
    assertion(X == 32).

test(clear_types) :-
    reset,
    add(x:int = y:int),
    (add((b:real = c:real) and (1 = 2)) -> true ;
     add(b:int = c:int)).

test(implied_and_consistent) :-
    reset,
    add(a > 10),
    is_implied(a > 1),
    \+ is_consistent(a < 5),
    \+ is_implied(a > 20).

:- end_tests(repl_tests).
