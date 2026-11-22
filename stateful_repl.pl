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

              timeout/1,
              reason_unknown/1,
              unsat_core/2,
              explain/2,
              relax/2,
              optimize/2,

              save_formulas/1,
              add_formulas/1,
              smtlib2/1,
              add_smtlib2/1,

              z3_help/0,

              % can this repetition be avoided?
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>),  % different-than
              op(739, xfy, <=>), % iff
              op(299, xfy, :)
          ]).

/** <module> Stateful REPL for Z3

Remembers added Z3 formulas and declarations from one query to the next, like the Z3 prompt or the
Python API. (z3.pl, in contrast, shares no state between queries, except for enumeration sorts.)

```prolog
?- add(x:int > 3).
?- add(y = x + 1).
?- implied(y > 4).
true.
?- model(M).
M = model{constants:[x=4, y=5], functions:[]}.
```

Each add/1 type-checks the formula against the types so far, declares its new symbols, and keeps it
only if it is consistent with the formulas added before; otherwise it fails and nothing changes.

*/

:- use_module(z3_swi_foreign, [
                  z3_assert/2,
                  z3_declarations/2,
                  z3_free_handle/1,
                  z3_model_lists/2,
                  z3_new_handle/1,
                  z3_remove_declaration/3,
                  z3_check/2,
                  z3_reason_unknown/2,
                  z3_set_timeout/2,
                  z3_solver_pop/3,
                  z3_solver_push/2,
                  z3_solver_scopes/2,
                  z3_solver_smtlib2/2,
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

% Unsat cores, explanations, relaxations and optimization are delegated to z3.pl (see via_z3pl/3).
:- use_module(z3, [
                  z3_push/1,
                  z3_unsat_core/2,
                  z3_explain/2,
                  z3_relax/2,
                  z3_optimize/2,
                  z3_smtlib2_formulas/2
              ]).

:- use_module(library(assoc)).

%! z3_help
%  Print help.
z3_help :- format(
          "Z3 repl help:
           add(F)              Add formula F; fails, changing nothing, if F is inconsistent or ill-typed
           implied(F)          Check if F is implied by the formulas added so far (also implies/1)
           consistent(F)       Check if F is consistent with the formulas added so far
           model(M)            Get a model of the formulas added so far
           formulas(L)         Get the list of formulas added so far, in order (also asserted/1)
           declarations(L)     Get the types of the symbols so far (decl/1 also shows Z3's)
           status(S)           Get the solver status (l_true, l_false, l_undef)
           show_status         Print the number of formulas, the status, and the number of declarations
           scopes(N)           Get the number of solver scopes, one per formula added
           timeout(Ms)         Limit each check to Ms milliseconds (0: no limit)
           reason_unknown(R)   Get why the last check had status l_undef, such as timeout
           unsat_core(Fs, C)   C: a subset of Fs that conflicts with the formulas added so far
           explain(Fs, C)      C: a minimal such subset
           relax(Fs, K)        K: a maximal subset of Fs consistent with them, preferring earlier ones
           optimize(Os, M)     M: a model that is best for the objectives Os (minimize(T), maximize(T),
                               soft(F), soft(F, Weight))
           save_formulas(File) Save the formulas added so far to File
           add_formulas(File)  Add the formulas saved in File
           smtlib2(S)          S: the formulas added so far, as SMT-LIB2
           add_smtlib2(S)      Add the assertions of S, an SMT-LIB2 script, one at a time
           reset               Remove all formulas and declarations (the timeout is kept)~n").

:- initialization(reset_globals).

% fails if the variable does not exist:
get_repl_handle(H) :- nb_current(repl_handle, H).
get_type_map(M) :- nb_current(typecheck_map, M).
set_type_map(M) :- nb_setval(typecheck_map, M).

% The formulas added so far, in the order added.
get_recorded_formulas(L) :- nb_current(recorded_formulas, L).
set_recorded_formulas(L) :- nb_setval(recorded_formulas, L).

record_formula(F) :- get_recorded_formulas(L),
                     append(L, [F], New),
                     set_recorded_formulas(New).

repl_timeout(Ms) :- ( nb_current(repl_timeout, Ms) -> true ; Ms = 0 ).

% we should call reset_globals if there is a chance for the context to be invalidated
% before we do a reset. Otherwise, we'll have an old invalid pointer as the solver.

clear_globals :- (nb_current(repl_handle, H) -> (
                                                    z3_free_handle(H),
                                                    nb_delete(repl_handle)
                                                )
                 ; true),
                 empty_assoc(Empty),
                 set_type_map(Empty),
                 set_recorded_formulas([]).


reset_globals :- clear_globals,
                 z3_new_handle(H),
                 repl_timeout(Ms),
                 z3_set_timeout(H, Ms),
                 nb_setval(repl_handle, H).

% push_formula(+Formula, -NewMap, -NewSymbols, -Status): type-checks Formula, declares its new
% symbols, pushes a solver scope, asserts Formula and checks. Fails, undoing everything, if Formula is
% ill-typed or cannot be asserted; if the check is interrupted (call_with_time_limit/2, Ctrl-C), undoes
% everything and passes the exception on.
push_formula(Formula, NewMap, NewSymbols, Status) :-
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
    catch(( z3_assert(Handle, FG_notypes) -> z3_check(Handle, Status) ; Status = not_asserted ),
          Error,
          ( undo_push(NewSymbols), throw(Error) )),
    (   Status == not_asserted
    ->  undo_push(NewSymbols),
        fail
    ;   true
    ).

% Pops the scope push_formula/4 pushed, and removes the declarations it added.
undo_push(NewSymbols) :-
    get_repl_handle(Handle),
    z3_solver_pop(Handle, 1, _),
    remove_declarations(NewSymbols).

remove_one(H, F/N) :- z3_remove_declaration(H, F, N).
remove_declarations(L) :-
    get_repl_handle(H),
    maplist(remove_one(H), L). % all declarations should have the form F/N

%! add_formula(+F)
%  Adds Z3 formula F. Typechecks and adds resulting declarations as well.
%  If the formula is inconsistent with other formulas so far, fails,
%  and the context is unchanged. If Z3 cannot decide (status `l_undef`, for example after a
%  timeout), F is added, with a warning.
add_formula(F) :- push_formula(F, NewMap, NewSymbols, Status),
                  (member(Status, [l_false, l_type_error])  -> (
                                           undo_push(NewSymbols),
                                           fail
                                        )
                  ; (
                      set_type_map(NewMap),
                      record_formula(F),
                      (   Status == l_undef
                      ->  reason_unknown(Reason),
                          print_message(warning, z3_message("Added %w, but Z3 could not check it (%w): the formulas may be inconsistent", [F, Reason]))
                      ;   true
                      )
                  )).

%! decl(-M)
%  Get all declarations, in both prolog and Z3 versions.
decl(M) :-
    get_repl_handle(H),
    z3_declarations(H, Z),
    declarations(D),
    M = {z3:Z, pl:D}.

%% user-visible:

%! add(+F) is semidet.
%  Adds formula F, if it is well typed and consistent with the formulas added so far; otherwise
%  fails, and nothing changes. Shortcut for add_formula/1.
add(F) :- add_formula(F).

%! asserted(-List) is det.
%  List is the formulas added so far, in the order added.
asserted(L) :- get_recorded_formulas(L).

%! formulas(-List) is det.
%  List is the formulas added so far, in the order added (alias for asserted/1).
formulas(L) :- get_recorded_formulas(L).

%! reset is det.
%  Removes all formulas and declarations. The timeout (timeout/1) is kept.
reset :- reset_globals.

%! declarations(-List) is det.
%  Get all Prolog declarations, constructed by the type checker, as a list of `term-type` pairs.
declarations(L) :- get_type_map(M),
                   assoc_to_list(M, L).

%! model(-Model) is semidet.
%  Get a Z3 model for the formulas asserted so far.
% Note that Z3 can return "uncertain" models if the status is `l_undef`.
model(Model) :- get_repl_handle(H),
                status(_),
                z3_model_lists(H, Model).

model_assoc(Model) :- get_repl_handle(H),
                      z3_model_assocs(H, Model).

%! scopes(-N) is det.
%  N is the number of solver scopes: one for each formula added so far.
scopes(N) :- get_repl_handle(H),
             z3_solver_scopes(H, N).

push_check_and_pop(F, Status) :-
    push_formula(F, _NewMap, NewSymbols, Status),
    undo_push(NewSymbols).

%! implied(+Formula) is semidet.
%  Succeeds iff `Formula` is known to be implied by the current asserted formulas. Fails if this can't
%  be proved, including when Z3 cannot decide (see reason_unknown/1).
implied(F) :- push_check_and_pop(not(F), Status),
              Status == l_false.

%! consistent(+Formula) is semidet.
%  Succeeds iff `Formula` is known to be consistent with the current asserted formulas, that is, check
%  status is `l_true`. Fails if this can't be proved, including when Z3 cannot decide.
consistent(F) :- push_check_and_pop(F, Status),
                 Status == l_true.

%! implies(+Formula) is semidet.
%  Alias for implied.
implies(X) :- implied(X).

%! status(-Status) is det.
%  Does a z3_check for the formulas asserted so far, returning the
%  status, one of (`l_true`, `l_false`, `l_undef`).
status(Status) :- get_repl_handle(H),
                  z3_check(H, Status).

%! timeout(+Milliseconds) is det.
%  Limits each check to Milliseconds: a check that runs out has status `l_undef`, with reason
%  `timeout` or `canceled` (see reason_unknown/1). 0 removes the limit. Kept by reset/0. It also
%  applies to unsat_core/2, explain/2, relax/2 and optimize/2.
timeout(Ms) :-
    must_be(nonneg, Ms),
    get_repl_handle(H),
    z3_set_timeout(H, Ms),
    nb_setval(repl_timeout, Ms).

%! reason_unknown(-Reason) is det.
%  Reason is why the last check had status `l_undef`, such as `timeout`.
reason_unknown(Reason) :-
    get_repl_handle(H),
    z3_reason_unknown(H, Reason).

%! unsat_core(+Formulas, -Core) is semidet.
%  Core is a subset of Formulas, in their order, that conflicts with the formulas added so far (see
%  z3_unsat_core/2). Fails if Formulas are consistent with them. Nothing is added.
unsat_core(Formulas, Core) :-
    must_be(list, Formulas),
    via_z3pl(Formulas, z3_unsat_core, Core).

%! explain(+Formulas, -Core) is semidet.
%  Core is a minimal subset of Formulas, in their order, that conflicts with the formulas added so
%  far: removing any formula from Core makes it consistent (see z3_explain/2). Fails if Formulas are
%  consistent with them. Nothing is added.
explain(Formulas, Core) :-
    must_be(list, Formulas),
    via_z3pl(Formulas, z3_explain, Core).

%! relax(+Formulas, -Kept) is det.
%  Kept is a maximal subset of Formulas, in their order, that is consistent with the formulas added
%  so far, preferring earlier formulas when they conflict (see z3_relax/2). Nothing is added: to keep
%  them, add each of Kept.
relax(Formulas, Kept) :-
    must_be(list, Formulas),
    via_z3pl(Formulas, z3_relax, Kept).

%! optimize(+Objectives, -Model) is semidet.
%  Model is a model of the formulas added so far that is best for Objectives, a list in priority
%  order of `minimize(T)`, `maximize(T)`, `soft(F)` and `soft(F, Weight)` (see z3_optimize/2). Model
%  has an extra key, `objectives`, with each objective's value. Nothing is added.
optimize(Objectives, Model) :-
    must_be(list, Objectives),
    via_z3pl_goal(z3_optimize(Objectives, M), M, Model).

% via_z3pl(+Formulas, +Predicate, -Subset): calls Predicate(Formulas, Subset0) with z3.pl, with the
% formulas added so far pushed first, and gives the corresponding subset of the caller's Formulas
% (not copies, as the result comes out of findall/3).
via_z3pl(Formulas, Predicate, Subset) :-
    Goal =.. [Predicate, Formulas, Subset0],
    via_z3pl_goal(( Goal, positions(Subset0, Formulas, Positions) ), Positions, Found),
    include_positions(Formulas, 1, Found, Subset).

% via_z3pl_goal(+Goal, +Template, -Result): runs Goal with z3.pl, with the formulas added so far
% pushed first, in order, and the REPL's timeout; Result is Template's copy. The pushes are undone by
% findall/3, so z3.pl's own formulas are unaffected. Fails if Goal fails.
via_z3pl_goal(Goal, Template, Result) :-
    get_recorded_formulas(Recorded),
    repl_timeout(Ms),
    ( nb_current(z3_timeout, Old) -> true ; Old = 0 ),
    setup_call_cleanup(z3:z3_set_timeout(Ms),
                       findall(Template, ( maplist(z3_push, Recorded), Goal ), Found),
                       z3:z3_set_timeout(Old)),
    Found = [Result].

% The positions in Formulas of the elements of Subset, a sublist of Formulas.
positions(Subset, Formulas, Positions) :-
    findall(I, ( nth1(I, Formulas, F), member(S, Subset), S == F ), Positions0),
    sort(Positions0, Positions).

include_positions([], _, _, []).
include_positions([F|Fs], I, Positions, Subset) :-
    I1 is I + 1,
    (   memberchk(I, Positions)
    ->  Subset = [F|Rest]
    ;   Subset = Rest
    ),
    include_positions(Fs, I1, Positions, Rest).

%! save_formulas(+Filename)
%  Saves the formulas added so far, in order, to the given Filename (an atom or a string).
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

%! smtlib2(-String) is det.
%  String is the formulas added so far as an SMT-LIB2 benchmark, for other SMT solvers
%  (see z3_solver_smtlib2/2).
smtlib2(String) :-
    get_repl_handle(H),
    z3_solver_smtlib2(H, String).

%! add_smtlib2(+String) is semidet.
%  Adds the assertions of String, an SMT-LIB2 script that declares what it uses, one at a time, as
%  add/1 does (see z3_smtlib2_formulas/2). Fails at the first one that is inconsistent with the
%  formulas added so far, or ill-typed; those before it stay added.
add_smtlib2(String) :-
    z3_smtlib2_formulas(String, Formulas),
    maplist(add, Formulas).

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

test(model) :-
    reset,
    add(x:int > 3),
    add(y = x + 1),
    model(M),
    memberchk(x = X, M.constants),
    memberchk(y = Y, M.constants),
    assertion(Y =:= X + 1).

% The formulas are kept in the order added, duplicates included: one per scope.
test(formulas_in_order) :-
    reset,
    add(z:int > 1),
    add(a:int > 0),
    add(z:int > 1),
    formulas(L),
    assertion(L == [z:int > 1, a:int > 0, z:int > 1]),
    scopes(N),
    assertion(N == 3).

% A failed add changes nothing: formulas, scopes and declarations are as before.
test(failed_add_changes_nothing, [forall(member(F, [x < 2, y:int = true, f(x) = "s" and f(x) = 1]))]) :-
    reset,
    add(x:int > 3),
    assertion(\+ add(F)),
    formulas(L), assertion(L == [x:int > 3]),
    scopes(N), assertion(N == 1),
    declarations(D), assertion(D == [x/0-int]),
    status(S), assertion(S == l_true).

% An add stopped while Z3 checks (here by call_with_time_limit/2) changes nothing either, and the
% REPL still works afterwards.
test(interrupted_add_changes_nothing) :-
    reset,
    add(x:int > 3),
    catch(call_with_time_limit(0.5, add(forall([k:int], g(k) > k))), time_limit_exceeded, true),
    formulas(L), assertion(L == [x:int > 3]),
    scopes(N), assertion(N == 1),
    declarations(D), assertion(D == [x/0-int]),
    status(S), assertion(S == l_true).

% With a timeout, Z3 gives up (or stops by itself, as incomplete for quantifiers): an undecided add is
% kept, with a warning, and the reason is available.
test(timeout, [setup(timeout(300)), cleanup((timeout(0), reset))]) :-
    reset,
    add(forall([k:int], g(k) > k)),
    formulas(L), assertion(L == [forall([k:int], g(k) > k)]),
    reason_unknown(R),
    assertion(atom(R)).

test(timeout_kept_by_reset, [cleanup((timeout(0), reset))]) :-
    timeout(300),
    reset,
    assertion(nb_current(repl_timeout, 300)).

test(unsat_core) :-
    reset,
    add(x:int > 3),
    unsat_core([y:int = 1, x < 2, y > 0], Core),
    assertion(Core == [x < 2]),
    formulas(L), assertion(L == [x:int > 3]).

test(unsat_core_consistent, [fail]) :-
    reset,
    add(x:int > 3),
    unsat_core([x < 9], _).

test(explain) :-
    reset,
    add(x:int > 3),
    explain([x < 9, x < 2, y:int = 1], Core),
    assertion(Core == [x < 2]).

% The result is made of the caller's own terms, in their order.
test(explain_caller_terms) :-
    reset,
    add(x:int > 3),
    Fs = [x < 9, x < 2, x < 1],
    explain(Fs, [C]),
    assertion(memberchk(C, [x < 2, x < 1])).

test(relax) :-
    reset,
    add(x:int > 3),
    relax([x < 9, x < 2, y:int = 1, x > 5], Kept),
    assertion(Kept == [x < 9, y:int = 1, x > 5]),
    formulas(L), assertion(L == [x:int > 3]).

test(optimize) :-
    reset,
    add(x:int >= 0 and y:int >= 0 and x + y =< 10),
    optimize([maximize(2 * x + y)], M),
    assertion(M.objectives == [maximize(2 * x + y) = 20]),
    formulas(L), assertion(length(L, 1)).

test(save_and_restore, [setup(tmp_file_stream(text, File, S)), cleanup(delete_file(File))]) :-
    close(S), delete_file(File),
    reset,
    add(s:string = "héllo"),
    add(b:int = 2),
    add(c:int > b),
    save_formulas(File),
    reset,
    add_formulas(File),
    formulas(L),
    assertion(L == [s:string = "héllo", b:int = 2, c:int > b]).

test(smtlib2_round_trip) :-
    reset,
    add(x:int > 3),
    add(r:real = x / 2.0),
    add(b:bv(8) = int2bv(8, 7)),
    smtlib2(S),
    assertion(sub_string(S, _, _, _, "(declare-fun x () Int)")),
    reset,
    add_smtlib2(S),
    formulas(L),
    assertion(length(L, 3)),
    assertion(implied(r > 1.5)).

test(add_smtlib2_inconsistent, [fail]) :-
    reset,
    add(x:int > 3),
    add_smtlib2("(declare-const x Int) (assert (< x 2))").

:- end_tests(repl_tests).
