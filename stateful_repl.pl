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
              implied/1,
              consistent/1,
              status/1,
              show_status/0,

              save_formulas/1,
              add_formulas/1,

              z3_help/0,

              % can this repetition be avoided?
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>),  % different-than
              op(739, xfy, <=>), % iff
              op(299, xfy, :)
          ]).
    
/** <module> Stateful REPL for Z3

Remembers asserted Z3 formulas and declarations from one query to the next.

*/

:- use_module(z3_swi_foreign, [
                  z3_assert/2,
                  z3_declarations/2,
                  z3_free_handle/1,
                  z3_model_lists/2,
                  z3_new_handle/1,
                  z3_remove_declaration/3,
                  z3_check/2,
                  z3_solver_pop/3,
                  z3_solver_push/2,
                  z3_solver_scopes/2,
                  z3_model_assocs/2
              ]).

:- use_module(z3_utils, [
                  z3_declare_types_for_symbols/3,
                  ground_version/3,
                  remove_type_annotations/2,
                  z3_expand_term/2
              ]).

:- use_module(type_inference, [
                  typecheck/4
              ]).

:- use_module(library(assoc)).

% TODO: allow adding inconsistencies, add explain/relax?

%! z3_help
%  Print help.
z3_help :- format(
          "Z3 repl help:
           add(F)              Add formula F
           consistent(F)       Check if F is consistent with what has been added so far
           implies(F)          Check if F is implied by what has been added so far
           formulas(L)         Get list of formulas asserted so far
           status(S)           Get solver status (l_true, l_false, l_undef)
           model(M)            Get a model for formulas added so far, if possible
           reset               Reset all declarations"),
           true.

% z3.pl shares no state between queries, except for enum declarations.

% this code, in contrast, shares everything: the solver, the type declarations, and the enums.

% can still pop the stack. Surgically remove assertions?
% also saves the session to disk to resume later

:- initialization(reset_globals).

% fails if the variable does not exist:
get_repl_handle(H) :- nb_current(repl_handle, H).
get_type_map(M) :- nb_current(typecheck_map, M).
set_type_map(M) :- nb_setval(typecheck_map, M).

get_recorded_formulas(L) :- nb_current(recorded_formulas, L).
set_recorded_formulas(L) :- nb_setval(recorded_formulas, L).

record_formula(F) :- get_recorded_formulas(L),
                     ord_add_element(L, F, New),
                     set_recorded_formulas(New).

get_asserted(M) :- nb_current(asserted_formulas, M).

% we should call reset_globals if there is a chance for the context to be invalidated
% before we do a reset. Otherwise, we'll have an old invalid pointer as the solver.

clear_globals :- (nb_current(repl_handle, H) -> (
                                                    z3_free_handle(H),
                                                    nb_delete(repl_handle)
                                                )
                 ; true),
                 set_type_map(t),
                 set_recorded_formulas([]).


reset_globals :- clear_globals,
                 z3_new_handle(H),
                 nb_setval(repl_handle, H),
                 true.

push_formula(Formula, NewMap, NewSymbols, Status) :-
    %% must_be(ground, Formula),
    get_type_map(OldAssoc),
    z3_expand_term(Formula, FormulaTransformed),
    ground_version(FormulaTransformed, FG, Symbols),
    (typecheck(FG, bool, OldAssoc, NewMap) -> true ;
     print_message(error, z3_message("Type error for %w", [FG])),
     fail
     ),
    !, %% commit to first solution
    exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
    get_repl_handle(Handle),
    z3_declare_types_for_symbols(Handle, NewSymbols, NewMap),
    z3_solver_push(Handle, _),
    remove_type_annotations(FG, FG_notypes),
    z3_assert(Handle, FG_notypes),
    z3_check(Handle, Status).


remove_one(H, F/N) :- z3_remove_declaration(H, F, N).
remove_declarations(L) :-
    get_repl_handle(H),
    maplist(remove_one(H), L). % all declarations should have the form F/N

%! add_formula(+F)
%  Adds Z3 formula F. Typechecks and adds resulting declarations as well.
%  If the formula is inconsistent with other formulas so far, fails,
%  and the context is unchanged.
add_formula(F) :- push_formula(F, NewMap, NewSymbols, Status),
                  (member(Status, [l_false, l_type_error])  -> (
                                           get_repl_handle(Handle),
                                           z3_solver_pop(Handle, 1, _),
                                           remove_declarations(NewSymbols),
                                           fail
                                        )
                  ; (
                      set_type_map(NewMap),
                      record_formula(F)
                  )).

%! decl(-M)
%  Get all declarations, in both prolog and Z3 versions.
decl(M) :-
    get_repl_handle(H),
    z3_declarations(H, Z),
    declarations(D),
    M = {z3:Z, pl:D}.
    
%% user-visible:

%! add(+F)
%  Shortcut for add_formula
add(F) :- add_formula(F).

%! asserted(-List)
%  Get list of asserted formulas.
asserted(L) :- get_recorded_formulas(L).

%! formulas(-List)
%  Get list of asserted formulas (alias for `asserted`).
formulas(L) :- get_recorded_formulas(L).

%! reset
%  Clear all asserted formulas and declarations.
reset :- reset_globals.

%! declarations(-List)
%  Get all Prolog declarations, constructed by the type checker, as a list of `term-type` pairs.
declarations(L) :- get_type_map(M),
                   assoc_to_list(M, L).

%! model(-Model)
%  Get a Z3 model for the formulas asserted so far.
% Note that Z3 can return "uncertain" models if the status is `l_undef`.
model(Model) :- get_repl_handle(H),
                status(_),
                z3_model_lists(H, Model).

model_assoc(Model) :- get_repl_handle(H),
                      z3_model_assocs(H, Model).

%! scopes(-N)
%  Get the number of scopes for the (implicit) solver.
%  Should be generally equal to the number of formulas asserted so far.
scopes(N) :- get_repl_handle(H),
             z3_solver_scopes(H, N).

push_check_and_pop(F, Status) :-
    push_formula(F, _NewMap, NewSymbols, Status),
    get_repl_handle(H),
    z3_solver_pop(H, 1, _),
    remove_declarations(NewSymbols).

%! implied(+Formula)
%  Succeeds iff `Formula` is known to be implied by the current asserted formulas. Fails if this can't be proved.
implied(F) :- push_check_and_pop(not(F), Status),
              Status == l_false.

%% todo: handle l_undef

%! consistent(+Formula)
%  Succeeds iff `Formula` is known to be consistent with the current asserted formulas, that is, check status is `l_true`. Fails if this can't be proved.
consistent(F) :- push_check_and_pop(F, Status),
                 Status == l_true.

%! implies(+Formula)
%  Alias for implied.
implies(X) :- implied(X).

%! status(-Status)
%  Does a z3_check for the formulas asserted so far, returning the
%  status, one of (`l_true`, `l_false`, `l_undef`).
status(Status) :- get_repl_handle(H),
                  z3_check(H, Status).
    
/****
%% give option to pop last asserted thing? But types remain...
%% Could include in the stack the new tupes introduced at each step, erase them on pop.
z3_pop(Formula) :-
    must_be(var, Formula),
    pop_recorded_formulas(Formula),
    get_repl_handle(S),
    z3_solver_pop(S).               
****/

%! save_formulas(+Filename)
%  Saves the set of added formulas to the given Filename (an atom or a string).
%  Fails if the file exists.
save_formulas(Filename) :-
    (exists_file(Filename) -> (write("File exists"), fail) ; true),
    open(Filename, write, Output, [create([all])] ),
    formulas(L),
    write_canonical(Output, L), %% fast_write fails?
    writeln(Output, "."),
    close(Output).

%! add_formulas(+Filename)
%  Reads formulas from the given filename, adds them to the current set.
add_formulas(Filename) :-
    open(Filename, read, Input),
    read(Input, L),
    close(Input),
    maplist(add, L),
    show_status.

%! show_status
%  Prints summary of current status.
show_status :-
    formulas(L),
    length(L, Len),
    print_message(informational, z3_message("There are %w added formulas", [Len])),
    status(Status),
    print_message(informational, z3_message("Status is %w", [Status])),
    get_type_map(M),
    assoc_to_list(M, ML),
    length(ML, NumDecl),
    print_message(informational, z3_message("Type map has %w declarations", [NumDecl])),
    true.

:- begin_tests(repl_tests,
               [setup(reset), cleanup(clear_globals)]
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
     implied(a > 1),
     \+ consistent(a < 5),
     \+ implied(a > 20).

:- end_tests(repl_tests).
