%%% -*- Mode: Prolog; Module: z3; -*-.

% The user-visible functions rely on an implicit solver, pushed and popped automatically, and a backtrackable type map:

:- module(z3, [
              solver_scopes/1,         % -Scopes  Number of solver scopes at the current depth, from 0
              z3_check/1,              % ?Status  Status of the global solver: l_true, l_false or l_undef
              z3_check_and_print/1,    % ?Status  The same, printing a model if possible
              z3_set_timeout/1,        % +Milliseconds  Limit each check of the global solver (0: no limit)
              z3_reason_unknown/1,     % -Reason  Why the last check returned l_undef
              z3_unsat_core/2,         % +Formulas, -Core  A subset of Formulas inconsistent with the solver
              z3_minimal_core/2,       % +Formulas, -Core  The same, minimal (using QuickXplain)
              z3_explain/2,            % +Formulas, -Core  A minimal subset of Formulas that is inconsistent
              z3_relax/2,              % +Formulas, -Kept  A maximal subset of Formulas that is consistent
              z3_optimize/2,           % +Objectives, -Model  An optimal model of the formulas pushed so far
              z3_declarations/1,       % -Declarations  Declarations so far, or those of the previous query (reset on a new push)
              z3_declare_enum/2,       % +EnumName, +EnumValues  Declares an enumeration sort. Not backtrackable.
              z3_declare_datatype/2,   % +Name, +Constructors  Declares an algebraic datatype. Not backtrackable.
              z3_declare_datatypes/1,  % +[Name-Constructors, ...]  The same, for mutually recursive datatypes
              z3_datatypes/1,          % -Datatypes  The datatypes declared, enumerations included
              z3_enum_declarations/1,  % -Declarations  The enumeration sorts declared so far
              z3_eval/2,               % +Expression, -Result  Evaluates Expression in a model, if the solver is sat
              z3_eval/3,               % +Expression, +Completion, -Result  The same, with a completion flag
              z3_is_consistent/1,      % +Formula  Formula is consistent with the formulas pushed. Fails if l_undef.
              z3_is_implied/1,         % +Formula  Formula follows from the formulas pushed. Fails if l_undef.
              z3_label/1,              % +Vars  Binds Vars to values from models, a new solution on backtracking
              z3_model/1,              % -Model  A model of the formulas pushed. Fails if status is l_false.
              z3_model_assocs/1,       % -Model  The same, with assoc maps (less readable)
              z3_push/1,               % +Formula  Pushes Formula; fails if l_false or ill-typed
              z3_push/2,               % +Formula, ?Status  Pushes Formula, giving the status (also l_type_error)
              z3_push_and_print/1,     % +Formula  Pushes and prints a model; fails unless l_true
              z3_push_and_print/2,     % +Formula, ?Status  Pushes and prints a model
              z3_reset/0,              % Resets everything: a new handle, no declarations or enums
              z3_smtlib2/1,            % -String  The formulas pushed so far, as SMT-LIB2
              z3_smtlib2_formulas/2,   % +String, -Formulas  An SMT-LIB2 script's assertions, typed for z3_push
              z3_push_smtlib2/1,       % +String  Pushes an SMT-LIB2 script's assertions
              free_globals/0,          % Frees the global handle

              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>),  % different-than
              op(739, xfy, <=>), % iff
              op(299, xfy, :)
              % {}/1, % clashes with other CLP libraries
              ]).

/** <module> Z3 high-level integration (backtrackable version)

This module builds on the basic functionality of z3_swi_foreign.pl to provide:

- Typechecking and declaring Z3 variables and functions.
- Attributed variables.
- Pushing and popping assertions on the solver as we assert and backtrack.
- Models, consistency and implication checks, and evaluation.
- Unsat cores, minimal explanations and relaxations of conflicting formulas.
- Optimization, and timeouts.

For incrementality, this module maintains a global_handle, where the push and pops happen.
So even though it is a single Z3 C object, kept in a non-backtrackable Prolog variable, it is meant to work as a backtrackable one.

type_inference_global_backtrackable does keep a --- backtrackable --- type map.

@author Tomas Uribe
@license MIT
*/

:- use_module(type_inference_global_backtrackable, [
                  initialize_map/0 as initialize_type_inference_map,
                  assert_type/2,
                  assert_formula_list_types/1,
                  get_map/1 as get_type_inference_map,
                  set_map/1 as set_type_inference_map,
                  get_map_list/1 as get_type_inference_map_list
              ]).

:- use_module(type_inference, [
                  mappable_symbol/1,
                  quantifier/3
              ]).

:- use_module(z3_utils, [
                  ground_version/3,
                  remove_type_annotations/2,
                  reset_var_counts/0,
                  valid_status_list/1,
                  z3_declare/3,            % +Handle, +Formula,+Type    Declares Formula to have Type.
                  z3_declare_types_for_symbols/3,
                  z3_enum_declarations_assoc/2,
                  z3_datatype_declarations_assoc/2,
                  z3_expand_term/2
                  ]
             ).
:- use_module(quickexplain, [qexplain/3, qrelax/3]).  % for z3_explain/2 and z3_relax/2

:- use_module(utils, [repeat_string/3,
                      pair_list_to_assoc/2
                     ]).

:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(debug)).   % debug/3, for the z3(handle) topic

:- use_module(z3_swi_foreign, [
                  z3_assert/2,
                  z3_declarations/2,
                  z3_declarations_string/2,
                  z3_declare_enum/3,
                  z3_declare_datatypes/2,
                  z3_datatypes/2,
                  z3_declare_function/3,
                  z3_enum_declarations/2,
                  z3_enums_string/2,
                  z3_free_handle/1,
                  z3_free_model/2,
                  z3_get_model/2,
                  z3_model_eval/5,
                  z3_model_lists/2,
                  z3_model_assocs/2,
                  z3_new_handle/1,
                  z3_reset_declarations/1,
                  z3_check/2,
                  z3_check_and_print/2,
                  z3_set_timeout/2,
                  z3_reason_unknown/2,
                  z3_check_assumptions/3,
                  z3_get_unsat_core/2,
                  z3_optimize/5,
                  z3_solver_pop/3,
                  z3_solver_push/2,
                  z3_solver_scopes/2,
                  z3_solver_smtlib2/2,
                  z3_parse_smtlib2/4
              ]).

:- initialization(new_global_handle(_)).

free_handle :-
    (nb_current(global_handle, H) ->
         (
             debug(z3(handle), "Freeing old z3.pl handle", []),
             z3_free_handle(H)
         )
    ;
    true),
    nb_delete(global_handle).


%! z3_reset
%  Resets the entire Z3 context. All declarations, including enums, are cleared.
%  Old models and solvers are invalidated.
z3_reset :-
    %% assertion(b_getval(solver_depth, 0)), %% test cleanup violates this
    free_handle,
    assertion(\+ get_global_handle(_)),
    new_global_handle(_).

%! free_globals
%  Frees all the implicit global variables, including the Z3 context.
free_globals :-
    free_handle,
    true.
    

%% To automatically pop the Z3 server when backtracking:
%% solver_depth is a backtrackable variable, with the depth level.
%% Before an assert, we check that variable, and pop the solver as many times as needed to match it.

%% indent according to solver pushes:
report(K, T) :- indent(T, R),
                print_message(K, z3_message(R)).

report(K, F, Vars) :- swritef(String, F, Vars),
                      report(K, String).

indent(Message, R) :- assert_depth(N),
                      repeat_string("----", N, S),
                      atomics_to_string([S,Message], R).

%  Resets all declarations and solver, including enums:
reset_globals :-
    new_global_handle(_),
    reset_var_counts,
    initialize_type_inference_map.

%! z3_declare_enum(+EnumName,+ValueList)
%  Declares the given enum type, as ranging over the given list of values.
z3_declare_enum(N,V) :- get_global_handle(H),
                        z3_declare_enum(H,N,V),
                        add_datatype_functions_to_type_map(H).

%! z3_declare_datatype(+Name, +Constructors) is det.
%  Declares the algebraic datatype Name, with Constructors: each an atom, or a term C(Field:Sort, ...),
%  where a Sort can be Name itself, for a recursive datatype. For each constructor C, this declares C,
%  the recognizer is_C/1, and an accessor Field/1 for each field. For example:
%
%      z3_declare_datatype(list, [nil, cons(head:int, tail:list)])
%
%  makes `cons(1, nil)` a list, `head(L)` and `tail(L)` its parts, and `is_cons(L)` true for a non-empty
%  list. Like z3_declare_enum/2, this is not undone by backtracking, and z3_reset/0 clears it. See
%  z3_declare_datatypes/1 for datatypes that refer to each other.
z3_declare_datatype(Name, Constructors) :-
    z3_declare_datatypes([Name-Constructors]).

%! z3_declare_datatypes(+Datatypes) is det.
%  Declares the datatypes in Datatypes, a list of Name-Constructors, together, so that they can refer
%  to each other (see z3_declare_datatype/2 and z3_declare_datatypes/2 in z3_swi_foreign). Raises
%  `permission_error(declare, ...)` for a constructor, recognizer or field name that is a built-in
%  name, such as `select` or `and`, or already declared.
z3_declare_datatypes(Datatypes) :-
    must_be(list, Datatypes),
    forall(( member(_-Cs, Datatypes), is_list(Cs), member(C, Cs), datatype_function_name(C, Name) ),
           (   mappable_symbol(Name)
           ->  true
           ;   permission_error(declare, function, Name)
           )),
    (get_global_handle(H) -> true ; new_global_handle(H)),
    z3_declare_datatypes(H, Datatypes),
    add_datatype_functions_to_type_map(H).

% The names a constructor declares: its own, its recognizer's, and its fields'.
datatype_function_name(C, Name) :-
    callable(C),
    functor(C, CName, _),
    (   Name = CName
    ;   atom_concat(is_, CName, Name)
    ;   compound(C), arg(_, C, Field), nonvar(Field), Field = Name:_, atom(Name)
    ).

% Adds the functions of the datatypes (and enumerations) of H to the current type map, which
% otherwise only gets them at the first push of a query.
add_datatype_functions_to_type_map(H) :-
    z3_datatype_declarations_assoc(H, New),
    get_type_inference_map(Map0),
    assoc_to_list(New, Pairs),
    foldl([K-V, M0, M]>>put_assoc(K, M0, V, M), Pairs, Map0, Map),
    set_type_inference_map(Map).

%! z3_datatypes(-Datatypes) is det.
%  Datatypes is the datatypes declared so far, enumeration sorts included, as
%  `datatype(Name, Constructors)`.
z3_datatypes(Datatypes) :-
    get_global_handle(H),
    z3_datatypes(H, Datatypes).

%! z3_enum_declarations(-DeclList) is det.
%  DeclList is the current enumeration sorts, with their values.
z3_enum_declarations(D) :- get_global_handle(H),
                           z3_enum_declarations(H, D).

%! z3_declarations(-DeclList) is det.
%  DeclList is the current declarations of constants and functions, as `(Name/Arity):Sort` terms.
z3_declarations(D) :- get_global_handle(H),
                      z3_declarations(H, D).

%%%%%%%%%%%%%%%%%%%%% Attribute variables %%%%%%%%%%%%%%%%%%%%%%%

attribute_goals(V) :- get_attr(V, z3, Attr),
                      z3_push(==(V, Attr), R),
                      \+ R = l_false.

%% Worth keeping an inverse map of "fake Z3 constants" to Prolog vars? Might need it for eval...
attr_unify_hook(Attr, Var) :- get_attr(Var, z3, Other), !,
                              debug(z3(unify), "Unifying two Z3 variables, ~w and ~w", [Attr, Other]),
                              z3_push(==(Attr, Other), R),
                              \+ R = l_false.
attr_unify_hook(Attr, Var) :- var(Var), !,
                              add_z3_attribute(Var, Attr).
attr_unify_hook(Attr, Formula) :-
    %% report(informational, status("Hook got", Attr, Formula)),
    z3_push(==(Attr, Formula), R), \+ (R = l_false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% should only be called at the top-most level.
%% Making and freeing handles is traced under the debug topic z3(handle), off by default:
%% ?- debug(z3(handle)).  shows it.

new_global_handle(Handle) :-
    debug(z3(handle), "Making new z3.pl handle", []),
    free_handle,
    z3_new_handle(Handle),
    (nb_current(z3_timeout, Ms) -> z3_set_timeout(Handle, Ms) ; true), % kept across z3_reset
    nb_setval(global_handle, Handle),
    nb_setval(solver_depth, 0),
    debug(z3(handle), "Made new z3.pl handle", []).

get_global_handle(Handle) :- nb_current(global_handle, Handle).

%% get_or_make_global_handle(H) :-
    

assert_depth(N) :- b_getval(solver_depth, N).

z3_declare(A,B) :-
    get_global_handle(H),
    z3_declare(H,A,B).

z3_declare(A) :-
    get_global_handle(H),
    z3_declare(H,A).

%% we should only use push_solver to get the solver.
%% and it should always be called before an assert, if we want it to be retractable.
%% So, hide push_solver, expose asserts.

push_solver(S) :- get_global_handle(S),
                  resolve_solver_depth(X),
                  New is X + 1,
                  b_setval(solver_depth, New), %% backtrackable assignment
                  z3_solver_push(S, _D).


raw_solver_scopes(N) :- get_global_handle(S), z3_solver_scopes(S, N).

%% Pops the Z3 solver to match the PL solver_depth:
resolve_solver_depth(X) :- b_getval(solver_depth, X),
                           raw_solver_scopes(N),
                           resolve_solver_depth(X, N).


resolve_solver_depth(X, Scopes) :- X >= Scopes,
                                   % report(informational, status("scopes OK", Scopes, X)),
                                   !.
resolve_solver_depth(X, Scopes) :- X < Scopes,
                                   % report(informational, status("need to pop", Scopes, X)),
                                   Numpops is Scopes - X,
                                   popn(Numpops).

popn(Numpops) :- get_global_handle(S),
                 (  z3_solver_pop(S, Numpops, _)
                 -> true
                 ; report(error, "error popping Z3 solver\n")
                 ).

%% user-visible:

%! solver_scopes(-N)
%  Number of scopes for the solver at current backtracking point
solver_scopes(N) :- resolve_solver_depth(_), raw_solver_scopes(N).

% should not be used directly. Types in Formula could clash with previously defined types,
% so should use z3_push. Also the matter of push and pop.
internal_assert_and_check(Solver, Formula, Status) :-
    z3_assert(Solver, Formula),
    z3_check(Solver, Status).

%! z3_set_timeout(+Milliseconds) is det.
%  Limits each check of the global solver to Milliseconds; a check that runs out has status `l_undef`,
%  with reason `timeout` or `canceled` (see z3_reason_unknown/1). 0 removes the limit. The limit is kept when
%  z3_reset/0 makes a new handle. To limit one call instead, call_with_time_limit/2 also works.
z3_set_timeout(Ms) :-
    (get_global_handle(H) -> true ; new_global_handle(H)),
    z3_set_timeout(H, Ms),
    nb_setval(z3_timeout, Ms).

%! z3_reason_unknown(-Reason) is det.
%  Reason is why the last check of the global solver had status `l_undef`, such as `timeout`.
z3_reason_unknown(Reason) :-
    get_global_handle(H),
    z3_reason_unknown(H, Reason).

%! z3_optimize(+Objectives, -Model) is semidet.
%  Model is an optimal model of the formulas pushed so far, for Objectives: a list, in priority
%  order, of `minimize(T)`, `maximize(T)`, `soft(F)` and `soft(F, Weight)` (see z3_optimize/5 in
%  z3_swi_foreign). Model is like z3_model/1's, with an extra key, `objectives`, pairing each
%  objective with its value: `[maximize(2*x+y) = 20]`. Values can contain `oo` (infinity) and
%  `epsilon` (an infinitesimal) for optima that are infinite or not attained. Fails if the formulas
%  are inconsistent, or Z3 cannot decide (status `l_undef`, for example after a timeout). The
%  solver is left as it was.
z3_optimize(Objectives, Model) :-
    must_be(list, Objectives),
    % findall/3 undoes the push that typechecks and declares the objectives. Only ground results
    % come out, and they are paired with the Objectives themselves, which may contain variables.
    findall(M-Values, optimal_model(Objectives, M, Values), Found),
    resolve_solver_depth(_),
    Found = [Model0-Values],
    maplist([O, V, O = V]>>true, Objectives, Values, Pairs),
    Model = Model0.put(objectives, Pairs).

optimal_model(Objectives, Model, Values) :-
    maplist(objective_formula, Objectives, Formulas),
    Conjunction =.. [and, true | Formulas],
    push_formula(Conjunction, types_only, l_true),  % types and declares the objectives' symbols
    ground_version(Objectives, Grounded, _),
    remove_type_annotations(Grounded, Plain),
    get_global_handle(H),
    z3_optimize(H, Plain, l_true, Values, M),
    z3_swi_foreign:z3_model_lists(H, M, Model),
    z3_free_model(H, M).

% A tautology that mentions an objective's expression, so typechecking gives its symbols types.
objective_formula(minimize(T), T = T) :- !.
objective_formula(maximize(T), T = T) :- !.
objective_formula(soft(F), or(F, not(F))) :- !.
objective_formula(soft(F, _Weight), or(F, not(F))) :- !.
objective_formula(O, _) :- domain_error(z3_objective, O).

%! z3_unsat_core(+Formulas, -Core) is semidet.
%  Core is a subset of Formulas, in their order, that is inconsistent with the formulas pushed so far.
%  Fails if Formulas are consistent with them, or if Z3 cannot decide (status `l_undef`). The solver
%  is left as it was. Z3 keeps cores small, but they need not be minimal; see z3_minimal_core/2.
%  If the pushed formulas are inconsistent by themselves, Core is `[]`.
%  Each formula F is asserted as `implies(Label, F)`, for a fresh Boolean Label, and the check is
%  made under the Labels as assumptions (z3_check_assumptions/3).
z3_unsat_core(Formulas, Core) :-
    must_be(list, Formulas),
    length(Formulas, N),
    numlist_labels(N, Labels),
    % findall/3 undoes the push; only the ground labels come out, so Formulas are not copied.
    findall(CoreLabels, core_labels(Formulas, Labels, CoreLabels), Found),
    resolve_solver_depth(_),          % pop the labelled formulas now, not at the next push
    Found = [CoreLabels],
    labelled_subset(Labels, Formulas, CoreLabels, Core).

%! z3_minimal_core(+Formulas, -Core) is semidet.
%  Like z3_unsat_core/2, but Core is minimal: removing any formula from it makes it consistent with
%  the formulas pushed so far. The unsat core is a fast first cut, which z3_explain/2 then minimizes.
%  With quantifiers, z3_explain/2's consistency checks of subsets may each take until the timeout.
z3_minimal_core(Formulas, Core) :-
    z3_unsat_core(Formulas, Core0),
    (   Core0 == []
    ->  Core = []                                % the pushed formulas are inconsistent by themselves
    ;   z3_explain(Core0, Core)
    ).

%! z3_explain(+Formulas, -Core) is semidet.
%  Core is a minimal subset of Formulas, in their order, that is inconsistent with the formulas pushed
%  so far: removing any formula from Core makes it consistent. Fails if Formulas are consistent with
%  them (or Z3 cannot decide). Uses QuickXplain (quickexplain.pl) with z3_push, but first types all of
%  Formulas together: pushed one at a time, a formula can get other types than with the rest (in
%  f(a) = f(b), a and f have no numeric type yet, so a = 1 alone is then a type error), and
%  qexplain(z3_push, ...) would take that type error for a conflict. If the formulas pushed so far are
%  inconsistent by themselves, Core is []. Raises a type_error if Formulas are not well typed together.
%  The solver is left as it was.
z3_explain(Formulas, Core) :-
    typed_quickxplain(explain, Formulas, Core).

%! z3_relax(+Formulas, -Kept) is det.
%  Kept is a maximal subset of Formulas, in their order, that is consistent with the formulas pushed so
%  far: adding any other formula of Formulas makes it inconsistent. When formulas conflict, earlier
%  ones are preferred, so list the most important first. Kept is Formulas if they are consistent.
%  Like z3_explain/2, it types all of Formulas together first, and raises a type_error if they are not
%  well typed together. Kept is [] if the formulas pushed so far are inconsistent by themselves. The
%  solver is left as it was.
z3_relax(Formulas, Kept) :-
    typed_quickxplain(relax, Formulas, Kept).

% Runs QuickXplain (Mode explain or relax) on Formulas, typed together first. QuickXplain runs on
% numbered formulas inside findall/3, which undoes the pushes; only the numbers come out, so
% Formulas, which may contain Prolog variables, are not copied.
typed_quickxplain(Mode, Formulas, Result) :-
    must_be(list, Formulas),
    length(Formulas, N),
    numlist(0, N, [0|Is]),                           % numlist(1, 0, _) fails, so start from 0
    pairs_keys_values(Numbered, Is, Formulas),
    catch(findall(Numbers, quickxplain_numbers(Mode, Formulas, Numbered, Numbers), Found),
          Error,
          ( resolve_solver_depth(_), throw(Error) )),
    resolve_solver_depth(_),
    Found = [Numbers],
    % Not findall/3, which would copy: the result must be the caller's own terms, in their order.
    include([I-_]>>memberchk(I, Numbers), Numbered, Chosen),
    pairs_values(Chosen, Result).

quickxplain_numbers(Mode, Formulas, Numbered, Numbers) :-
    Conjunction =.. [and, true | Formulas],
    (   push_formula(Conjunction, types_only, l_true)    % types and declares all the symbols together
    ->  true
    ;   type_error(well_typed_formulas, Formulas)
    ),
    (   \+ \+ z3_push(true, l_false)
    ->  Chosen = []                                      % the pushed formulas are inconsistent by themselves
    ;   conjunction_status(Conjunction, Formulas, Status),
        quickxplain_mode(Mode, Status, Numbered, Chosen)
    ),
    pairs_keys(Chosen, Numbers).

% Status is the status of pushing Conjunction. Pushing it also makes Z3 check what type inference
% cannot, such as sorts it only infers itself; a formula Z3 cannot build is a type error, which
% QuickXplain would otherwise take for a conflict.
conjunction_status(Conjunction, Formulas, Status) :-
    findall(S, z3_push(Conjunction, S), Statuses),
    (   Statuses = [Status], Status \== l_type_error
    ->  true
    ;   type_error(well_typed_formulas, Formulas)
    ).

quickxplain_mode(explain, l_false, Numbered, Core) :-   % fails unless Formulas are inconsistent
    qexplain(push_consistent, Numbered, Core).
quickxplain_mode(relax, Status, Numbered, Kept) :-
    (   Status == l_true
    ->  Kept = Numbered                                % consistent: keep them all
    ;   reverse(Numbered, Reversed),                   % qrelax keeps later formulas over earlier ones
        qrelax(push_consistent, Reversed, Kept)
    ).

% The push QuickXplain uses: fails only if the solver becomes inconsistent. Every formula was
% checked as part of the conjunction, so a type error should not happen, but would raise an error
% rather than look like a conflict.
push_consistent(_-F) :-
    (   z3_push(F, Status), Status \== l_type_error
    ->  Status \== l_false
    ;   type_error(well_typed_formula, F)
    ).

numlist_labels(0, []) :- !.
numlist_labels(N, Labels) :-
    numlist(1, N, Is),
    maplist([I, L]>>format(atom(L), "$core_~w", [I]), Is, Labels).

core_labels(Formulas, Labels, CoreLabels) :-
    maplist([F, L, implies(L:bool, F)]>>true, Formulas, Labels, Implications),
    Conjunction =.. [and, true | Implications],
    z3_push(Conjunction, Status),
    (   Status == l_false
    ->  CoreLabels = []                % inconsistent without any of Formulas
    ;   memberchk(Status, [l_true, l_undef]),
        get_global_handle(H),
        z3_check_assumptions(H, Labels, l_false),
        z3_get_unsat_core(H, CoreLabels)
    ).

labelled_subset([], [], _, []).
labelled_subset([L|Ls], [F|Fs], CoreLabels, Core) :-
    (   memberchk(L, CoreLabels) -> Core = [F|Core1] ; Core = Core1 ),
    labelled_subset(Ls, Fs, CoreLabels, Core1).

%! z3_check(-Status)
%  Do a solver check and return the status, one of `{l_true, l_false, l_undef}`
z3_check(Status) :-
    check_status_arg(Status),
    resolve_solver_depth(_),          % drop formulas undone by backtracking
    get_global_handle(S),
    z3_check(S, Status).

%! z3_check_and_print(-Status)
%  Prints a model if status is not `l_false` (that is, known to be unsat).
z3_check_and_print(Status) :-
    check_status_arg(Status),
    resolve_solver_depth(_),
    get_global_handle(Solver),
    z3_check_and_print(Solver, Status).

% Flag toggles between getting the model as lists or as assoc maps:
z3_model_internal(Flag, Model) :-
    must_be(oneof([lists, assocs]), Flag),
    resolve_solver_depth(_),
    z3_check(Status),
    member(Status, [l_true, l_undef]), !,
    get_global_handle(H),
    (Flag == lists -> z3_model_lists(H, Model) ; z3_model_assocs(H, Model)).

%! z3_model(-Model) is semidet.
%  Model is a model of the formulas pushed so far, as described for z3_model_lists/2 in
%  z3_swi_foreign: `model{constants:[x=1, ...], functions:[...]}`. Fails if the formulas are
%  inconsistent. If Z3 cannot decide (status `l_undef`), the model may not satisfy them.
z3_model(Model) :- z3_model_internal(lists, Model).


%! z3_model_assocs(-Model) is semidet.
%  Like z3_model/1, with assoc maps instead of lists.
z3_model_assocs(Model) :- z3_model_internal(assocs, Model).

check_status_arg(Status) :- valid_status_list(L),
                            must_be((var; oneof(L)), Status).

%% We now use backtrackable types in Prolog, resetting declarations at the first push.
%% Note that type declarations in Z3 can't be pushed and popped.
%% We could allow different types on different branches if new declarations overwrite old ones without error.

%% Note that z3_push(false, R) will still push "false" onto the solver.

%! z3_push(+Formula, ?Status) is det.
%  Typechecks Formula against the formulas pushed so far, declares its new symbols, pushes it onto the
%  global solver, and checks. Status is `l_true`, `l_false`, `l_undef` (Z3 could not decide, as after a
%  timeout) or `l_type_error` (Formula is not pushed). Does not fail on `l_false`: the inconsistent
%  formula stays pushed; see z3_push/1. The push is undone on backtracking. If Status is given, fails
%  unless the status is that one.
z3_push(Foriginal, Status) :-
    check_status_arg(Status),
    push_formula(Foriginal, assert, Status).

% push_formula(+Formula, +Mode, -Status): z3_push/2 for Mode = assert; for Mode = types_only, only types
% and declares Formula's symbols and pushes a solver scope, without asserting or checking (Status is
% l_true unless there is a type error).
push_formula(Foriginal, Mode, Status) :-
    (get_global_handle(H) -> true; new_global_handle(H)),
    z3_expand_term(Foriginal, F),
    (b_getval(solver_depth, 0) ->
         z3_reset_declarations(H), %% does not clear enums
         z3_datatype_declarations_assoc(H, EnumMap), %% enumeration values and datatype functions
         set_type_inference_map(EnumMap)
    ; true),
    get_type_inference_map(OldAssoc),
    %% report(status("asserting", F)),
    ground_version(F, FG, Symbols),
    %% updates the type inference map:
    (assert_type(FG, bool) ->
         (
             %% Only need to declare new symbols:
             exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
             %% writeln(compare(Symbols, NewSymbols)),
             get_type_inference_map(Assoc),
             z3_declare_types_for_symbols(H, NewSymbols, Assoc),
             push_solver(Solver),
             %% We now remove ":" terms from FG. Unfortunately, this can't be done by "ground_version", because
             %% we use the ":" annotations in the type checking after variables are grounded (assert_type);
             %% so we do two passes through the term.
             remove_type_annotations(FG, FG_notypes),
             (   Mode == assert
             ->  internal_assert_and_check(Solver, FG_notypes, Status)
             ;   Status = l_true
             )
         )
    ;  (
        Status = l_type_error,
        get_type_inference_map_list(L),
        report(error, "Type error in term: %w. Type map was %w", [FG, L])
    )
    ).


%! z3_push(+Formula) is semidet.
%  Like z3_push/2, but fails, pushing nothing, if Formula is inconsistent with the formulas pushed so far
%  (`l_false`) or ill-typed. Succeeds with `l_true`, and with `l_undef` (Z3 could not decide).
z3_push(F) :- z3_push(F, R), (R == l_true ; R == l_undef), !.

solve(L, M) :- maplist(z3_push, L), z3_model(M).

%! z3_eval(+Expression, +CompletionFlag, -Result)
%  Evaluates the expression in a current model. CompletionFlag is one of `true, false`.
z3_eval(Expression, Completion, Result) :-
    \+ is_list(Expression), !,
    resolve_solver_depth(_),
    get_global_handle(S),
    z3_check(S, l_true),
    replace_var_attributes(Expression, E1),
    setup_call_cleanup(
        z3_get_model(S, Model),
        z3_model_eval(S, Model, E1, Completion, Result),
        z3_free_model(S, Model)
    ).
z3_eval(L, C, R) :-
    is_list(L), !,
    z3_eval_list(L, C, R).

%! z3_eval(+Expression, -Result)
%  Evaluates the expression in a current model, with `false` as the completion flag.
z3_eval(Expression, Result) :- z3_eval(Expression, false, Result).

%% Map eval on a list:
z3_eval_list(L, Completion, Result) :- must_be(list, L),
                                       resolve_solver_depth(_),
                                       get_global_handle(S),
                                       z3_check(S, l_true),
                                       replace_var_attributes(L, L1),
                                       setup_call_cleanup(
                                           z3_get_model(S, Model),
                                           maplist({Model, Completion}/[X]>>z3_model_eval(S, Model, X, Completion), L1, Result),
                                           z3_free_model(S, Model)
                                       ).


%% A little inefficient for big terms, might be better to do in the C code eval:
replace_var_attributes(X, A) :- var(X), get_attr(X, z3, A), !, true.
replace_var_attributes(X, X) :- \+ compound(X), !, true.
replace_var_attributes(X, R) :- compound(X),
                                mapargs(replace_var_attributes, X, R).


%% NOTES: If we declare uninterpreted types, say, for a=b, later on assert a=1, then the type for a would change.
%% But Z3 does not let us change types, so this case is not handled. (Ideally, we would equate them, adding "uninterpreted = int").

get_term_for_var(X, T) :- var(X),
                          add_z3_attribute(X, T).


/*
internal_assert_and_check_list(Solver, List, Status) :-
    Conj =.. [and | List],
    internal_assert_and_check(Solver, Conj, Status).
*/

%! z3_label(+Vars) is nondet.
%  Binds each Prolog variable in Vars to its value in a model of the formulas pushed so far, so that the
%  variables satisfy them; on backtracking, gives another solution, with a different value for at least
%  one of the variables, until there are no more. Elements of Vars that are already bound are left
%  alone. Each unbound one must occur in a formula pushed so far (that gives it its Z3 constant);
%  otherwise raises instantiation_error. Fails if the formulas are inconsistent, or Z3 cannot decide.
%  With infinitely many solutions (x > 0 over the integers), it never runs out. Values of uninterpreted
%  sorts, such as 'foo!val!0', do not work: given back to Z3, they are read as new constants.
z3_label(Vars) :-
    must_be(list, Vars),
    include(var, Vars, Free),
    maplist(variable_constant, Free, Constants),
    label_constants(Free, Constants).

variable_constant(V, C) :-
    (   get_attr(V, z3, C)
    ->  true
    ;   instantiation_error(V)
    ).

label_constants([], []) :- !.
label_constants(Vars, Constants) :-
    z3_eval(Constants, true, Values),     % true: values even for constants no formula constrains
    (   Vars = Values                     % binding pushes each Constant == Value (attr_unify_hook/2)
    ;   maplist([C, V, not(C = V)]>>true, Constants, Values, Different),
        Another =.. [or, false | Different],
        z3_push(Another),                 % undone on backtracking, like any push
        label_constants(Vars, Constants)
    ).

%! z3_smtlib2(-String) is det.
%  String is the formulas pushed so far, as an SMT-LIB2 benchmark: the declarations they need, then
%  the `assert`s (see z3_solver_smtlib2/2 in z3_swi_foreign). Other SMT solvers can read it.
z3_smtlib2(String) :-
    resolve_solver_depth(_),            % drop formulas undone by backtracking
    get_global_handle(H),
    z3_solver_smtlib2(H, String).

%! z3_smtlib2_formulas(+String, -Formulas) is semidet.
%  Formulas is the assertions of String, an SMT-LIB2 script, as formulas for z3_push/1, in order: each
%  use of a function or constant the script declares is annotated with its sort (x:int,
%  f(A:int):real), so that type inference gives every symbol the script's sort. String must declare
%  everything it uses, except built-ins; it is parsed on its own, without the formulas pushed so far.
%  Its datatypes (`declare-datatypes`, enumerations included) are declared, as by
%  z3_declare_datatypes/1, unless they already are, with the same constructors; like
%  z3_declare_datatypes/1, this is not undone by backtracking. Fails, printing Z3's message, if
%  String does not parse.
z3_smtlib2_formulas(String, Formulas) :-
    setup_call_cleanup(z3_new_handle(H),
                       z3_parse_smtlib2(H, String, Formulas0, Declarations),
                       z3_free_handle(H)),
    ensure_datatypes(Declarations),
    maplist(annotate_formula(Declarations), Formulas0, Formulas).

% Declares the datatypes in Declarations (datatype(Name, Constructors) terms, from z3_parse_smtlib2/4)
% that are not declared yet, together, since they can refer to each other. One already declared must
% have the same constructors.
ensure_datatypes(Declarations) :-
    (get_global_handle(H) -> true ; new_global_handle(H)),
    z3_datatypes(H, Existing),
    findall(Name-Cs,
            ( member(datatype(Name, Cs), Declarations),
              (   memberchk(datatype(Name, Old), Existing)
              ->  ( Old == Cs -> fail ; domain_error(datatype(Name, Old), Cs) )
              ;   true
              ) ),
            New),
    (   New == []
    ->  true
    ;   z3_declare_datatypes(New)
    ).

%! z3_push_smtlib2(+String) is semidet.
%  Pushes the assertions of String, an SMT-LIB2 script (see z3_smtlib2_formulas/2), one at a time.
%  Fails if one of them is inconsistent with the formulas pushed so far, or ill-typed with them.
z3_push_smtlib2(String) :-
    z3_smtlib2_formulas(String, Formulas),
    maplist(z3_push, Formulas).

% Annotates each use of a declared constant or function in F with its sort. Declarations are
% Name:Sort and Name(ArgSort, ...):Sort, as from z3_parse_smtlib2/4. A quantifier's bound variables
% shadow constants of the same name.
annotate_formula(Declarations, F, Annotated) :-
    annotate(F, Declarations, Annotated).

annotate(X, Ds, A) :-
    atom(X), !,
    (   memberchk(X:Sort, Ds), atom(X)
    ->  A = (X:Sort)
    ;   A = X
    ).
annotate(X, _, X) :- \+ compound(X), !.
annotate(Q, Ds, A) :-
    quantifier(Q, Vars, Body), !,
    findall(Name, (member(V, Vars), (V = Name:_ -> true ; V = Name)), Bound),
    exclude([N:_]>>memberchk(N, Bound), Ds, Inner),
    annotate(Body, Inner, Body1),
    Q =.. [Quantifier, _, _],
    A =.. [Quantifier, Vars, Body1].
annotate(fp_value(V, S), _, fp_value(V, S)) :- !.            % a constant whose arguments are not terms
annotate(X, Ds, A) :-
    compound_name_arguments(X, Name, Args),
    maplist([Arg, Arg1]>>annotate(Arg, Ds, Arg1), Args, Args1),
    length(Args, N),
    length(ArgSorts, N),
    Template =.. [Name|ArgSorts],
    (   N > 0, memberchk(Template:Range, Ds)
    ->  maplist([Arg, S, (Arg:S)]>>true, Args1, ArgSorts, Typed),
        X1 =.. [Name|Typed],
        A = (X1:Range)
    ;   A =.. [Name|Args1]
    ).

%! z3_push_and_print(+Formula, -Status)
%  Pushes the formula, and prints a model.
z3_push_and_print(F,R) :- z3_push(F,R), z3_check_and_print(R1), assertion(R == R1).

%! z3_push_and_print(+Formula)
%  Pushes the formula, and prints a model. Fails if status is not `l_true` (sat).
z3_push_and_print(F) :- z3_push_and_print(F, l_true).

%! z3_is_consistent(+Formula) is semidet.
%  Succeeds if Formula is known to be consistent with the formulas pushed so far (status `l_true`). Fails
%  if it is not, or if Z3 cannot decide. Pushes nothing.
z3_is_consistent(F) :-
    check_and_pop(F, l_true).

% Pushes F, succeeding if the status is Status, then pops it again, restoring solver_depth: popping
% alone left solver_depth one too high, so that a later backtrack could leave a formula asserted.
% F's types stay in the type map, as its symbols stay declared in Z3, which does not undo
% declarations within a query.
check_and_pop(F, Status) :-
    b_getval(solver_depth, Depth),
    z3_push(F, Status),
    popn(1),
    b_setval(solver_depth, Depth).

%% to handle type errors correctly, need to distiguish failure-by-type-error from failure-by-inconsistency:

%! z3_is_implied(+Formula) is semidet.
%  Succeeds if Formula is known to be implied by the formulas pushed so far (its negation is
%  inconsistent with them). Fails if it is not, if Z3 cannot decide, or if Formula is ill-typed. Pushes
%  nothing.
z3_is_implied(F) :-
    check_and_pop(not(F), l_false).

%% does not work if there are type errors:
%% z3_is_implied(F) :- \+ z3_is_consistent(not(F)).


{}(X) :- z3_push(X).


%%%%%%%%%%%%%%%%%%%%%%%%%% unit tests %%%%%%%%%%%%%%%%%


:- begin_tests(push_assert, [setup(reset_globals), cleanup(free_globals)]).

test_formulas(Formulas) :-
    Formulas = [foo(a) = b+c,
                foo(b) = 2,
                a = (b:int), %% int should remove choicepoint
                b = a,
                d:int = f(e:foobarsort),
                foo(b) = (c:int) % this implies b = 0
               ]
               .

check_test_formulas(Formulas, R) :-
    test_formulas(Formulas),
    Conjunction =.. [and | Formulas],
    z3_push(Conjunction, R).

test(sat, [true(R == l_true)] ) :-
    check_test_formulas(_F, R).

%% only tests type inference:
test(typetest, [true(A-F == int-lambda([foobarsort], int)) , nondet ] ) :-
    test_formulas(Formulas),
    assert_formula_list_types(Formulas),
    get_type_inference_map(Map),
    get_assoc(a/0, Map, A),
    get_assoc(f/1, Map, F).

test(nonsat, [true(R1 == l_true), true(R2 == l_false)] ) :-
    check_test_formulas(_Formulas, R1),
    assertion(z3_is_implied(b = 0)),
    z3_push(b=2, R2).

test(reals, [true(R == l_true)] ) :-
    z3_push(y:real > 2),
    z3_push(a:real=div(x, y)),
    z3_push(a = div(b:real, 4.0)),
    z3_push(a > 0.0, R).

% interesting scenario: z3_push(a:real = div(x, y), R), z3_push(a = div(b:real, 4.0), R1), z3_model(M).
% reports on division-by-zero value.
% also interesting:
% z3_push_and_print(a:real=div(x, y), R), z3_push_and_print(a = div(b, 4.0), R1).

test(atmost0, [true(R == l_true), true(R1 == l_false)] ) :-
    z3_push(atmost(a:bool, b:bool, c:bool, 0), R),
    z3_push(a, R1).

test(atmost1) :-
    z3_push(atmost(a:bool, b:bool, c:bool, 1), R), z3_push(a, R1), z3_push(b, R2),
    R = l_true,
    R1 = l_true,
    R2 = l_false.

test(atleast) :-
    z3_push(atleast(a:bool, b:bool, c:bool, 2), R),
    z3_push(a, R1),
    z3_push(not(b), R2),
    z3_push(not(c), R3),
    R = l_true,
    R1 = l_true,
    R2 = l_true,
    R3 = l_false.

test(consistent) :-
    z3_push(and(a:int>b, b>c, c>d)), \+ z3_is_consistent(d>a),
    z3_is_consistent(a > d),
    z3_push(a > d).

test(implied) :-
    z3_is_implied(true),
    \+ z3_is_implied(false),
    z3_push(and(a:int>b, b>c, c>d)), z3_is_implied(a>d).

test(implied_with_error) :-
    \+ z3_is_implied(x:foo = y:bar).

test(consistent_with_error) :-
    \+ z3_is_consistent(x:foo = y:bar).

test(boolean) :-
    z3_push(or(and(a:bool, b:bool), not(c:bool))),
    z3_push(c:bool),
    z3_is_implied(a).

test(eval, [true(R == 6)]) :-
    z3_push(a = 2),
    z3_push(b = 3),
    z3_eval(a * b, R).

test(eval_list, true(R == [3,4]) ) :-
    z3_push(a = 1),
    z3_push(b= 3),
    z3_eval([1+2, a + b], true, R).

test(undefs, [true(R2 == l_true)]) :-
    z3_push(power(a:real,b:int) = c, l_true), z3_push(c=2.0, R1), z3_push(a=2.0, R2),
    assertion(R1 == l_undef).

test(undef_implied) :-
    z3_push(power(a:real,b:int) = c, l_true), \+ z3_is_implied(c=2.0).

test(undef_consistent) :- % consistency check fails if l_undef
    z3_push(power(a:real,b:int) = c, l_true), \+ z3_is_consistent(c=2.0).

%% to see how the model changes:
%% z3:z3_push(b:int>c,R), z3:z3_push(and(a>d:int,b>e:int),R1), z3_push(f > b), z3_model(M), z3_is_consistent(f < a), z3_model(M1), z3_push(f > a), z3_model(M2).
%% or z3_push_and_print(a > 1), z3_push_and_print(b > 2), z3_push_and_print(a > b), solver_scopes(N).

test(scopes, [true(((N1 == 1), (N2==2))) ] ) :-
    solver_scopes(0),
    z3_push(a:int=14), solver_scopes(N1), z3_push(b:int=a-5), solver_scopes(N2).


test(between) :-
    z3_push(between(x:int, 1, 4)), z3_push(between(x, 2, 3)), z3_is_implied(x = 3 or x = 2).

test(instantiate_types, [true(X == 32)]) :-
    z3_push(a:bv(32) = b:bv(X), R),
    assertion(R == l_true),
    z3_push(c:T = d:int),
    assertion(T == int).

:- end_tests(push_assert).


:- begin_tests(attribute, [setup(reset_globals), cleanup(free_globals)]).

test(avar_succeeds) :-
    z3_push(X>10, R), X = 12, R = l_true.

test(aver_fails, [fail]) :-
    z3_push(X>10, _), X = 9.

test(avars_fail, [fail] ) :-
    z3_push(X:int>Y, _R),
    X = 10,
    Y = 14.

test(attributes1, [true(R==126)] ) :-
    z3_push(X=14), z3_push(Y=X-5), z3_eval(X * Y, R).

test(attributes2, [true(R==15) ] ) :-
    z3_push(X=14), z3_push(Y=X-5), Y=9, get_attr(X,z3,A), z3_eval(A+1,R).

test(attributes3, [true(R = 14)] ) :-
    z3_push(X=14), z3_push(Y > X), z3_push(_Z > Y), X = a, z3_eval(a,R).

test(attributes4, [fail] ) :-
    z3_push(X=14), z3_push(Y > X), z3_push(Z > Y), X = a, Z = a.

test(attribute_eval, [true(R == 126)]) :-
    z3_push(X=14), z3_push(Y=X-5), z3_eval(X*Y,R).

test(attribute_model) :-
    z3_push(X=14), z3_push(Y=X-5), z3_push(a = X-1), z3_push(b = Y*Y),
    z3_model(M),
    assertion(member(a=13, M.constants)),
    assertion(member(b=81, M.constants)).


test(isoneof) :-
    z3_push(isoneof(x:int, a, b, c)),
    z3_push(x <> a), z3_push(x <> c),
    z3_is_implied(x = b).

:- end_tests(attribute).

:- begin_tests(boolean, [setup(reset_globals), cleanup(free_globals)]).

test(bool_plus) :-
    z3_push((a:real) + (b:bool) = 3.0), z3_push(b), z3_model(M),
    M.constants == [a=2, b=true].

test(bool_times) :-
    z3_push((a:real) * (b:bool) = 0.0), z3_push(a = 3.2), z3_model(M),
    assertion(M.constants == [a=16/5, b=false]).

test(more_arith) :-
    z3_push(a:bool + b:real = 1.0), z3_model(M1), z3_push(b < 1), z3_model(M2),
    assertion(M1.constants == [a=false, b=1]),
    assertion(M2.constants == [a=true, b=0]).

test(bool_or) :-
    z3_push(((a;b))), z3_push(not(b)), z3_model(M),
    assertion(M.constants == [a=true, b=false]).

test(bool_and) :-
    z3_push((a,b)), z3_model(M),
    assertion(M.constants == [a=true, b=true]).

test(bool_andor, [fail]) :-
    z3_push((a,b)), z3_push(((not(a), not(b)))).

test(bool_implies) :-
    z3_push(a->b), z3_model(M),
    assertion(M.constants = [a=false]).

test(bool_iff) :-
    z3_push(a<=>b), z3_push(a), z3_model(M),
    assertion(M.constants = [a=true, b=true]).

test(type_error_scopes) :-
    z3_push(x:foo = y:bar, R), solver_scopes(S),
    assertion(R == l_type_error),
    assertion(S == 0).

%% makes sure that not(false) is popped after checking z3_is_implied(true):
test(is_implied_pop) :-
    z3_is_implied(true),
    \+ z3_is_implied(false).

test(int2real) :-
    z3_push(x = int2real(3)),
    z3_model(M),
    assertion(M.constants = [x=3]).

test(real2int) :-
    z3_push(x = real2int(3.3)),
    z3_model(M),
    assertion(M.constants = [x=3]).

test(isint) :-
    z3_push(is_int(3.0)),
    \+ z3_push(is_int(2)), %% should give type error
    z3_push(is_int(2), l_type_error).

test(ite_implies) :-
    z3_push(ite(x,y=1,y=2)),
    z3_push(not(x)),
    z3_is_implied(y = 2).

test(distinct) :-
    z3_push(distinct(a,b,c,d:int)),
    z3_is_implied(not(a=b)).

test(divides) :-
    z3_push(divides(3,x)),
    z3_push(x = 9, l_true),
    z3_push(divides(2,y)),
    z3_push(x = 5, l_false).

test(rem) :-
    z3_push(x = rem(14, 6)),
    z3_is_implied(x = 2).

test(nary_minus) :-
    z3_push(x:int = -(0,1,2,3,4)),
    z3_is_implied( x = -10 ).


test(nested_uninterpreted) :-
    z3_push(f(g(a,b)) = c),
    z3_model(_M).

:- end_tests(boolean).

:- begin_tests(z3pl_bitvectors, [setup(reset_globals), cleanup(free_globals)]).

test(basicor, [true((Ror == 9, Rand == 0))]) :-
    z3_push(a = int2bv(32, 1)),
    z3_push(b = int2bv(32, 8)),
    z3_eval(bvor(a,b), Ror),
    z3_eval(bvand(a,b), Rand).

test(neg_no_overflow, [true(C == [b=127])] )  :-
    z3_push(false = bvneg_no_overflow(bvnot(b:bv(8))), R),
    assertion(R = l_true),
    z3_model(M),
    M.constants = C.

test(mul_roundtrip) :-
    z3_push(bvmul(a:bv(32),b:bv(32)) = int2bv(32, 1)),
    z3_model(M),
    %% z3_eval(bvmul(int2bv(32,M.constants...)))
    M.constants = [a=A, b=B],
    z3_eval(bvmul(int2bv(32, A), int2bv(32, B)), R),
    assertion(R = 1).

%% fails for A=4, B=2
test(random_bv_xor) :-
    random_between(1, 63, Width), % z3_ast_to_term fails for 64
    High is (1<<Width) - 1,
    random_between(0, High, A), % inclusive
    random_between(0, High, B),
    C is A xor B,
    z3_eval(bvxor(int2bv(Width, A), int2bv(Width, B)), R),
    assertion(R == C).

test(push_numeral) :-
    Width = 63, %% TODO: fix Z3_ast_to_term for larger widths.
    findall(1, between(1,Width,_), L),
    z3_push(a = bv_numeral(L)),
    z3_push(signed = bv2int(a, true)),
    z3_push(unsigned = bv2int(a, false)),
    z3_model(_M).

test(combined_bvnumeral) :-
    z3_push(bvmul(a:bv(32),b:bv(32)) = int2bv(32, 1)),
    z3_push(bvuge(b, mk_numeral("1321", bv(32)))),
    z3_model(_M).

:- end_tests(z3pl_bitvectors).

:- begin_tests(large_numbers, [setup(reset_globals), cleanup(free_globals)] ).

test(large_mult) :-
    z3_push(x = 123434349499392931234343214**10),
    z3_model(_M).

test(rationals_test) :-
    z3_push(x = 3r5),
    z3_model_assocs(M),
    get_assoc(x, M.constants, 3/5).

% An irrational model value, algebraic(Approx, root(Coefficients, Index)), can be pushed back.
test(algebraic_round_trip) :-
    z3_push(x:real * x:real = 2.0 and x > 0.0),
    z3_model(M),
    memberchk(x = V, M.constants),
    assertion(V = algebraic(_, root([-2, 0, 1], 2))),
    z3_reset,
    z3_push(y:real = V),
    assertion(z3_is_implied(y * y = 2.0)),
    assertion(\+ z3_is_consistent(y > 1.5)).

:- end_tests(large_numbers).

% Built-in names that the type inference and the C code used to disagree about.

:- begin_tests(builtin_names, [setup(reset_globals), cleanup(free_globals)]).

% equal/2 was accepted by type inference but unknown to the C code.
test(equal) :-
    z3_push(equal(a:int, 3)),
    assertion(z3_is_implied(a = 3)).

% equals, minus and mod were unknown to type inference, so they were declared as
% uninterpreted functions as well as being handled as built-ins.
builtin_formula(equals(b:int, 4), b = 4).
builtin_formula(minus(c:int, 1) = 2, c = 3).
builtin_formula(mod(d:int, 3) = 1 and d > 0 and d < 3, d = 1).

test(no_function_declared, [forall(builtin_formula(F, Implied))]) :-
    z3_reset,
    z3_push(F),
    assertion(z3_is_implied(Implied)),
    z3_declarations(Ds),
    forall(member(D, Ds), assertion(D = ((_/0):_))).     % constants only

test(mod_is_integer_only, [fail]) :-
    z3_push(mod(e:real, 2.0) = 1.0).

% Type inference had these as bv2sub_..., both with three arguments.
test(bvsub_no_overflow) :-
    z3_push(bvsub_no_overflow(x:bv(8), y:bv(8))),
    z3_declarations(Ds),
    assertion(Ds == [(x/0):bv(8), (y/0):bv(8)]).

test(bvsub_no_underflow) :-
    z3_push(bvsub_no_underflow(x:bv(8), y:bv(8), true)).

:- end_tests(builtin_names).

% Strings through z3.pl's type inference.

:- begin_tests(z3pl_strings, [setup(reset_globals), cleanup(free_globals)]).

test(string_constraints) :-
    z3_push(s:string = str_concat("ab", t)),
    z3_push(str_len(s) = 5),
    z3_push(str_contains(s, "bc")),
    z3_model(M),
    memberchk(s = S, M.constants),
    assertion(string_length(S, 5)).

test(string_type_error) :-
    z3_push(str_len(x:int) = 3, R),
    assertion(R == l_type_error).

:- end_tests(z3pl_strings).

% The timeout for z3.pl's global solver, which survives z3_reset.

:- begin_tests(z3pl_timeout, [setup(reset_globals), cleanup((z3_set_timeout(0), free_globals))]).

% The pigeonhole problem with 9 pigeons and 8 holes, as one conjunction of clauses; it takes
% about 0.1 s to prove unsatisfiable, far longer than a 1 ms timeout.
pigeonhole_formula(F) :-
    findall(C, pigeonhole_clause(C), Cs),
    F =.. [and|Cs].
pigeonhole_clause(C) :- between(1, 9, I), findall(P, (between(1, 8, J), pigeonhole:pigeon(I, J, P)), Ps), C =.. [or|Ps].
pigeonhole_clause(not(and(A, B))) :- between(1, 8, J), between(1, 9, I), between(1, 9, K), I < K,
                                     pigeonhole:pigeon(I, J, A), pigeonhole:pigeon(K, J, B).

:- use_module(examples/pigeonhole, []).

test(timeout_survives_reset) :-
    z3_set_timeout(1),
    z3_reset,
    pigeonhole_formula(F),
    z3_push(F, Status),
    assertion(Status == l_undef),
    z3_reason_unknown(Reason),
    assertion(memberchk(Reason, [timeout, canceled])).   % depends on which part of Z3 stops

:- end_tests(z3pl_timeout).

% z3_unsat_core/2 and z3_minimal_core/2.

:- begin_tests(z3pl_cores, [setup(reset_globals), cleanup(free_globals)]).

test(core) :-
    z3_reset,
    z3_unsat_core([a:int > b, b > a, c:int = 1], Core),
    assertion(Core == [a:int > b, b > a]).

test(relative_to_pushed) :-
    z3_reset,
    z3_push(x:int > 5),
    z3_unsat_core([x < 3, y:int = 1, x < 0], Core),
    assertion(memberchk(Core, [[x < 3], [x < 0], [x < 3, x < 0]])).

test(consistent, [fail]) :-
    z3_reset,
    z3_push(x:int > 5),
    z3_unsat_core([x > 7, y:int = 1], _).

test(solver_unchanged) :-
    z3_reset,
    z3_push(x:int > 5),
    raw_solver_scopes(S0),
    z3_unsat_core([x < 3], _),
    raw_solver_scopes(S1),
    assertion(S1 == S0),
    get_global_handle(H),
    z3_swi_foreign:z3_solver_assertions(H, As),
    assertion(As == [x > 5]).                               % no labelled formulas left

test(already_inconsistent) :-
    z3_reset,
    z3_push(x:int > 5, _),
    z3_push(x < 3, l_false),
    z3_unsat_core([y:int = 1], Core),
    assertion(Core == []).

test(prolog_variables) :-
    z3_reset,
    z3_push(X > 10),
    z3_unsat_core([X < 5, Y > X, Y < 0], Core),
    Core = [Lt],
    assertion(Lt == (X < 5)).                               % the formula itself, not a copy

% QuickXplain pushes formulas one at a time; pushed alone, f(a) = f(b) left a, b and f without a
% numeric type, so a = 1 was a type error, which looked like a conflict.
test(minimal_core_types_formulas_together) :-
    z3_reset,
    Formulas = [f(a) = f(b), a = 1, b = 2, f(1) <> f(2)],
    z3_minimal_core(Formulas, Core),
    assertion(Core == Formulas).                            % all four are needed

test(minimal_core_like_qexplain) :-
    Formulas = [a:int = b, b:int = c, c:int = d, d:int = f(a), e:int = f(b), f(a:int) > f(d:int)],
    z3_reset,
    z3_minimal_core(Formulas, Core),
    z3_reset,
    qexplain(z3_push, Formulas, Expected),
    assertion(Core == Expected).

test(explain) :-
    z3_reset,
    z3_explain([x:int > 5, y:int = 1, x < 3], Core),
    assertion(Core == [x:int > 5, x < 3]).

test(explain_consistent, [fail]) :-
    z3_reset,
    z3_explain([x:int > 1, x < 3], _).

test(explain_relative_to_pushed) :-
    z3_reset,
    z3_push(x:int > 5),
    z3_explain([y:int = 1, x < 3], Core),
    assertion(Core == [x < 3]).

% Earlier formulas are preferred: of two that conflict, the earlier one is kept.
test(relax_prefers_earlier, [forall(member(Fs-Kept, [[x:int > 5, x < 3, y:int = 1]-[x:int > 5, y:int = 1],
                                                       [x:int < 3, x > 5, y:int = 1]-[x:int < 3, y:int = 1]]))]) :-
    z3_reset,
    z3_relax(Fs, K),
    assertion(K == Kept).

test(relax_consistent) :-
    z3_reset,
    z3_relax([x:int > 1, x < 3], Kept),
    assertion(Kept == [x:int > 1, x < 3]).

% Like z3_explain, z3_relax types the formulas together (qrelax(z3_push, ...) drops f(a) = f(b) here).
test(relax_types_formulas_together) :-
    z3_reset,
    z3_relax([f(a) = f(b), a = 1, b = 2, f(1) <> f(2)], Kept),
    assertion(Kept == [f(a) = f(b), a = 1, b = 2]).

test(explain_and_relax_leave_solver_unchanged) :-
    z3_reset,
    z3_push(x:int > 5),
    raw_solver_scopes(S0),
    z3_explain([x < 3], _),
    z3_relax([x < 3, x < 9], _),
    raw_solver_scopes(S1),
    assertion(S1 == S0),
    get_global_handle(H),
    z3_swi_foreign:z3_solver_assertions(H, As),
    assertion(As == [x > 5]).

test(explain_prolog_variables) :-
    z3_reset,
    z3_explain([X > 10, X < 5, Y > 0], Core),
    assertion(Core == [X > 10, X < 5]),                     % the caller's terms, not copies
    assertion(var(Y)).

test(explain_empty, [fail]) :-
    z3_reset,
    z3_explain([], _).

test(relax_empty) :-
    z3_reset,
    z3_relax([], Kept),
    assertion(Kept == []).

% If the formulas pushed so far conflict by themselves, none of the new ones is to blame.
test(explain_pushed_inconsistent) :-
    z3_reset,
    z3_push(x:int > 1),
    z3_push(x < 0, _),
    z3_explain([y:int > 0], Core),
    assertion(Core == []).

test(relax_pushed_inconsistent) :-
    z3_reset,
    z3_push(x:int > 1),
    z3_push(x < 0, _),
    z3_relax([y:int > 0], Kept),
    assertion(Kept == []).

test(explain_two_conflicts) :-
    z3_reset,
    z3_explain([x:int > 5, y:int > 5, x < 3, y < 3], Core),
    assertion(Core == [x:int > 5, x < 3]).

test(relax_two_conflicts) :-
    z3_reset,
    z3_relax([x:int > 5, y:int > 5, x < 3, y < 3], Kept),
    assertion(Kept == [x:int > 5, y:int > 5]).

% Formulas that are not well typed together are an error, not a conflict.
test(explain_type_error, [error(type_error(well_typed_formulas, _))]) :-
    z3_reset,
    z3_explain([x:int > 1, x = true], _).

test(relax_type_error, [error(type_error(well_typed_formulas, _))]) :-
    z3_reset,
    z3_relax([x:int > 1, x = true], _).

test(type_error_leaves_solver_unchanged) :-
    z3_reset,
    z3_push(y:int > 5),
    raw_solver_scopes(S0),
    catch(z3_relax([x:int > 1, x = true], _), error(type_error(_, _), _), true),
    raw_solver_scopes(S1),
    assertion(S1 == S0),
    z3_push(y < 9).

% Randomized checks against the definitions, over small sets of integer bounds:
%   z3_explain: the core is inconsistent, and removing any formula makes it consistent;
%   z3_relax: the kept formulas are consistent, and adding any other one makes them inconsistent;
%   both return a sublist of the input, in its order.

random_bound(F) :-
    random_member(V, [x, y]),
    random_between(0, 5, K),
    random_member(Op, [>, <, >=, =<, =, <>]),
    F0 =.. [Op, V:int, K],
    F = F0.

random_bounds(Fs) :-
    random_between(1, 6, N),
    length(Fs, N),
    maplist(random_bound, Fs).

consistent_formulas(Fs) :-
    Conjunction =.. [and, true | Fs],
    \+ \+ z3_push(Conjunction).

sublist_of([], _).
sublist_of([X|Xs], [Y|Ys]) :- ( X == Y -> sublist_of(Xs, Ys) ; sublist_of([X|Xs], Ys) ).

test(random_explain_minimal, [setup(set_random(seed(3)))]) :-
    forall(between(1, 60, _),
           (   random_bounds(Fs),
               z3_reset,
               (   z3_explain(Fs, Core)
               ->  assertion(sublist_of(Core, Fs)),
                   assertion(\+ consistent_formulas(Core)),
                   assertion(forall(select(_, Core, Rest), consistent_formulas(Rest)))
               ;   assertion(consistent_formulas(Fs))
               )
           )).

test(random_relax_maximal, [setup(set_random(seed(4)))]) :-
    forall(between(1, 60, _),
           (   random_bounds(Fs),
               z3_reset,
               z3_relax(Fs, Kept),
               assertion(sublist_of(Kept, Fs)),
               assertion(consistent_formulas(Kept)),
               assertion(forall(( member(F, Fs), \+ (member(K, Kept), K == F) ),
                                \+ consistent_formulas([F|Kept])))
           )).

:- end_tests(z3pl_cores).

% z3_optimize/2.

:- begin_tests(z3pl_optimize, [setup(reset_globals), cleanup(free_globals)]).

test(maximize) :-
    z3_reset,
    z3_push(x:int >= 0 and y:int >= 0 and x + y =< 10),
    z3_optimize([maximize(2*x + y)], M),
    assertion(M.constants == [x = 10, y = 0]),
    assertion(M.objectives == [maximize(2*x + y) = 20]).

test(soft) :-
    z3_reset,
    z3_push(not(p:bool and q:bool)),
    z3_optimize([soft(p, 2), soft(q)], M),
    assertion(M.objectives == [soft(p, 2) = true, soft(q) = false]).

% Symbols that only appear in objectives are typed and declared.
test(new_symbols) :-
    z3_reset,
    z3_push(x:int >= 0 and x =< 3),
    z3_optimize([soft(z:int =< 1), maximize(x + z)], M),
    assertion(M.objectives == [soft(z:int =< 1) = true, maximize(x + z) = 4]).

test(inconsistent, [fail]) :-
    z3_reset,
    z3_push(x:int > 0, _),
    z3_push(x < 0, _),
    z3_optimize([maximize(x)], _).

test(solver_unchanged) :-
    z3_reset,
    z3_push(x:int > 0),
    raw_solver_scopes(S0),
    z3_optimize([maximize(x), soft(y:int = 1)], _),
    raw_solver_scopes(S1),
    assertion(S1 == S0),
    get_global_handle(H),
    z3_swi_foreign:z3_solver_assertions(H, As),
    assertion(As == [x > 0]).

test(prolog_variables) :-
    z3_reset,
    z3_push(X >= 0),
    z3_push(X =< 5),
    z3_optimize([maximize(X)], M),
    M.objectives = [Objective = Value],
    assertion(Objective == maximize(X)),                    % the caller's variable, not a copy
    assertion(Value == 5).

:- end_tests(z3pl_optimize).

% Arrays through z3.pl's type inference.

:- begin_tests(z3pl_arrays, [setup(reset_globals), cleanup(free_globals)]).

test(model_and_round_trip) :-
    z3_reset,
    z3_push(select(a:array(int, int), 1) = 5),
    z3_push(select(a, 2) = 7),
    z3_model(M),
    memberchk(a = V, M.constants),
    z3_reset,
    z3_push(b:array(int, int) = V),
    assertion(z3_is_implied(select(b, 1) = 5 and select(b, 2) = 7)).

test(inferred_types) :-
    z3_reset,
    z3_push(select(store(c, 1, 2.5), i) > 2.0),
    z3_declarations(Ds),
    assertion(memberchk((c/0):array('Int', 'Real'), Ds)),
    assertion(memberchk((i/0):'Int', Ds)).

% An array whose element type is never determined gets an uninterpreted element sort.
test(unknown_element_sort) :-
    z3_reset,
    z3_push(a:array(int, _) = b),
    z3_declarations(Ds),
    assertion(memberchk((a/0):array('Int', uninterpreted), Ds)).

test(type_error) :-
    z3_reset,
    z3_push(select(e:array(int, int), "x") = 1, R),
    assertion(R == l_type_error).

:- end_tests(z3pl_arrays).

% Quantifiers through z3.pl: bound variables are typed in scope, and not declared.

:- begin_tests(z3pl_solver_depth, [setup(reset_globals), cleanup(free_globals)]).

% After resolving, Z3's scopes match the pushes on the current branch.
depth_matches :-
    resolve_solver_depth(D),
    raw_solver_scopes(N),
    assertion(D == N).

% Backtracking to a point between two pushes, after a consistency check, undoes the later push.
% (z3_is_consistent/1 and z3_is_implied/1 popped Z3 without lowering solver_depth, so x = 7
% stayed asserted.)
test(check_then_backtrack, [forall(member(Check, [z3_is_consistent(x > 5), z3_is_implied(x > -1)]))]) :-
    z3_reset,
    z3_push(x:int > 0),
    call(Check),
    depth_matches,
    z3_push(x < 10),
    member(K, [1, 2]),
    (   K == 1
    ->  z3_push(x = 7), fail
    ;   true
    ),
    assertion(z3_is_consistent(x = 3)),
    depth_matches.

% The checks push nothing; their formulas' types stay, as Z3 keeps the declarations.
test(checks_leave_nothing) :-
    z3_reset,
    z3_push(x:int > 0),
    z3_is_consistent(y:int > 0),               % not in assertion/1, which would undo the types
    z3_is_implied(x > -1),
    \+ z3_is_consistent(x < 0),
    \+ z3_is_implied(x > 3),
    depth_matches,
    get_global_handle(H),
    z3_swi_foreign:z3_solver_assertions(H, As),
    assertion(As == [x > 0]),
    z3_push(y:real > 0.5, Status),               % y is an int, from the check above
    assertion(Status == l_type_error).

% After backtracking, z3_check/1, z3_eval/2 and z3_model/1 see only the current branch.
test(no_stale_assertions) :-
    z3_reset,
    z3_push(x:int > 0),
    (   z3_push(x < 0, _), fail
    ;   true
    ),
    z3_check(S), assertion(S == l_true),
    z3_eval(x, V), assertion(V > 0),
    z3_model(M), assertion(memberchk(x = _, M.constants)).

:- end_tests(z3pl_solver_depth).

:- begin_tests(z3pl_division, [setup(reset_globals), cleanup(free_globals)]).

test(mixed_is_real_division) :-
    z3_reset,
    z3_push(x:int = 3),
    assertion(z3_is_implied(x / 2.0 = 1.5)),
    assertion(z3_is_implied(1.5 / x = 0.5)).

test(integers_divide_as_integers) :-
    z3_reset,
    z3_push(x:int = 7),
    assertion(z3_is_implied(x / 2 = 3)).

:- end_tests(z3pl_division).

:- begin_tests(z3pl_smtlib2, [setup(reset_globals), cleanup(free_globals)]).

test(export_after_backtracking) :-
    z3_reset,
    z3_push(x:int > 2),
    (   z3_push(y:int > x), fail
    ;   true
    ),
    z3_smtlib2(S),
    assertion(sub_string(S, _, _, _, "(assert (> x 2))")),
    assertion(\+ sub_string(S, _, _, _, "y")).

% Each use of a declared symbol is annotated with its sort, so that z3_push types it as the script did.
test(formulas_annotated) :-
    z3_smtlib2_formulas("(declare-const r Real) (declare-fun f (Int) Real) (assert (> r 2.0)) (assert (= r (f 3)))", Fs),
    assertion(Fs == [r:real > 2.0, r:real = f(3:int):real]).

% A bound variable shadows a constant of the same name.
test(quantifier_shadowing) :-
    z3_smtlib2_formulas("(declare-const x Int) (declare-fun h (Int) Int) (assert (forall ((x Int)) (> (h x) x))) (assert (= x 5))", Fs),
    assertion(Fs == [forall([x:int], h(x:int):int > x), x:int = 5]).

test(round_trip) :-
    z3_reset,
    z3_push(x:int > 2 and x < 4),
    z3_push(r:real = int2real(x) / 2.0),
    z3_push(s:string = str_concat("a", "b")),
    z3_push(q:float16 = fp_add(rne, fp_value(1, float16), fp_value(1, float16))),
    z3_smtlib2(S),
    z3_reset,
    z3_push_smtlib2(S),
    z3_model(M),
    assertion(memberchk(x = 3, M.constants)),
    assertion(memberchk(r = 3/2, M.constants)),
    assertion(memberchk(s = "ab", M.constants)),
    assertion(memberchk(q = fp_value(2.0, float16), M.constants)).

test(uninterpreted_sorts) :-
    z3_reset,
    z3_push_smtlib2("(declare-sort U 0) (declare-const a U) (declare-const b U) (declare-fun g (U) Int) (assert (distinct a b)) (assert (> (g a) (g b)))"),
    assertion(z3_is_implied(a <> b)).

test(inconsistent_fails, [fail]) :-
    z3_reset,
    z3_push(x:int > 5),
    z3_push_smtlib2("(declare-const x Int) (assert (< x 2))").

% Enumeration sorts are declared, and keep their values distinct, even after earlier pushes.
test(enumerations) :-
    z3_reset,
    z3_push(y:int > 0),
    z3_push_smtlib2("(declare-datatypes ((shade 0)) (((light) (dark)))) (declare-const s shade) (assert (not (= s light)))"),
    assertion(z3_is_implied(s = dark)),
    z3_enum_declarations(Ds),
    assertion(memberchk((dark/0):shade, Ds)).

test(enumeration_round_trip) :-
    z3_reset,
    z3_declare_enum(tone, [high, low]),
    z3_push(t:tone = high),
    z3_smtlib2(S),
    z3_reset,
    z3_push_smtlib2(S),
    assertion(z3_is_implied(t <> low)).

:- end_tests(z3pl_smtlib2).

:- begin_tests(z3pl_datatypes, [setup(reset_globals), cleanup(free_globals)]).

test(list) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_push(l:list = cons(1, cons(2, nil))),
    assertion(z3_is_implied(head(tail(l)) = 2)),
    assertion(z3_is_implied(is_cons(l))).

test(model) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_push(is_cons(t:list) and head(t) > 5 and is_nil(tail(t))),
    z3_model(M),
    M.constants = [t = cons(N, nil)],           % not in assertion/1, which would undo the binding
    assertion(N > 5).

% Constructors are distinct and injective, with no axioms to write.
test(free_constructors) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    assertion(z3_is_implied(cons(1, nil) <> nil)),
    assertion(z3_is_implied(implies(cons(a:int, nil) = cons(b:int, nil), a = b))).

% Type inference knows the datatype's functions: a field of the wrong sort is a type error.
test(typed) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_push(cons("s", nil) = l:list, Status),
    assertion(Status == l_type_error).

% Declared in the middle of a query, after a push, the datatype's functions are typed at once.
test(declared_mid_query) :-
    z3_reset,
    z3_push(n:int > 0),
    z3_declare_datatype(tree, [leaf, node(left:tree, value:int, right:tree)]),
    z3_push(t:tree = node(leaf, n, leaf)),
    assertion(z3_is_implied(value(t) > 0)).

test(mutual_recursion) :-
    z3_reset,
    z3_declare_datatypes([expr-[num(val:int), block(body:stmt)], stmt-[skip, eval(e:expr)]]),
    z3_push(x:expr = block(eval(num(3)))),
    assertion(z3_is_implied(val(e(body(x))) = 3)).

test(reserved_name, [error(permission_error(declare, function, select))]) :-
    z3_reset,
    z3_declare_datatype(bad, [select(a:int)]).

test(listed) :-
    z3_reset,
    z3_declare_datatype(point, [point(x:real, y:real)]),
    z3_declare_enum(color, [red, green]),
    z3_datatypes(Ds),
    msort(Ds, Sorted),
    assertion(Sorted == [datatype(color, [red, green]), datatype(point, [point(x:real, y:real)])]).

test(smtlib2_import) :-
    z3_reset,
    z3_push_smtlib2("(declare-datatypes ((L 0)) (((lnil) (lcons (lhd Int) (ltl L))))) (declare-const z L) (assert ((_ is lcons) z)) (assert (= (lhd z) 4))"),
    z3_model(M),
    assertion(M.constants == [z = lcons(4, lnil)]).

test(smtlib2_round_trip) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_push(l:list = cons(5, nil)),
    z3_smtlib2(S),
    z3_reset,
    z3_push_smtlib2(S),
    assertion(z3_is_implied(head(l) = 5)).

% With z3_label/1, Z3 finds lists of a given shape.
test(label) :-
    z3_reset,
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_push(L = cons(X, cons(Y, nil))),
    z3_push(X:int > 0 and Y:int > 0 and X + Y = 3),
    findall(L, z3_label([L]), Ls),
    msort(Ls, Sorted),
    assertion(Sorted == [cons(1, cons(2, nil)), cons(2, cons(1, nil))]).

:- end_tests(z3pl_datatypes).

:- begin_tests(z3pl_label, [setup(reset_globals), cleanup(free_globals)]).

test(all_solutions) :-
    z3_reset,
    findall(X-Y, (z3_push(X:int > 0 and Y:int > 0 and X + Y = 5), z3_label([X, Y])), L),
    msort(L, Sorted),
    assertion(Sorted == [1-4, 2-3, 3-2, 4-1]).

test(bound_elements_left_alone) :-
    z3_reset,
    findall(X, (z3_push(X:int > 2 and X < 5), Y = 1, z3_label([X, Y])), L),
    msort(L, Sorted),
    assertion(Sorted == [3, 4]).

test(only_the_given_variables) :-
    z3_reset,
    findall(X-U, (z3_push(X:int >= 0 and X < 2 and U:int > 7), z3_label([X])), L),
    assertion(length(L, 2)),
    forall(member(_-U, L), assertion(var(U))).

test(irrational) :-
    z3_reset,
    z3_push(Q:real * Q = 2.0 and Q > 0.0),
    z3_label([Q]),
    assertion(Q = algebraic(_, root([-2, 0, 1], 2))).

test(strings) :-
    z3_reset,
    findall(T, (z3_push(str_len(T:string) = 1 and str_lt(T, "b") and str_lt("_", T)), z3_label([T])), L),
    msort(L, Sorted),
    assertion(Sorted == ["`", "a"]).

test(inconsistent, [fail]) :-
    z3_reset,
    z3_push(X:int > 1, _),
    z3_push(X < 0, _),
    z3_label([X]).

test(unconstrained_variable, [error(instantiation_error)]) :-
    z3_reset,
    z3_label([_]).

test(nothing_to_label, [true(N == 1)]) :-
    z3_reset,
    aggregate_all(count, z3_label([]), N).

% Labeling pushes formulas, which are undone on backtracking: afterwards, the solver is as it was.
test(solver_unchanged) :-
    z3_reset,
    z3_push(x:int > 0 and x < 3),
    raw_solver_scopes(S0),
    \+ \+ (z3_push(X:int = x), findall(X, z3_label([X]), _)),
    z3_push(true),
    raw_solver_scopes(S1),
    assertion(S1 =:= S0 + 1).

:- end_tests(z3pl_label).

:- begin_tests(z3pl_quantifiers, [setup((reset_globals, z3_set_timeout(2000))),
                                  cleanup((z3_set_timeout(0), free_globals))]).

global_assertions(As) :- get_global_handle(H), z3_swi_foreign:z3_solver_assertions(H, As).

test(inferred_sort) :-
    z3_reset,
    z3_push(forall([x], f(x) * 0 = x * 0), _),             % x is an int; valid, so decided at once
    global_assertions(As),
    assertion(As == [forall([x:int], f(x) * 0 = x * 0)]),
    z3_declarations(Ds),
    assertion(\+ memberchk((x/0):_, Ds)),                   % the bound x is not a constant
    assertion(memberchk((f/1):'Int', Ds)).

test(implied) :-
    z3_reset,
    z3_push(forall([x], f(x) = 2 * x), _),
    assertion(z3_is_implied(f(5) = 10)).

% A sort that the body does not determine is uninterpreted.
test(unknown_sort) :-
    z3_reset,
    z3_push(forall([x], x = x), _),
    global_assertions(As),
    assertion(As == [forall([x:uninterpreted], x = x)]).

test(shadowing) :-
    z3_reset,
    z3_push(x:bool),
    z3_push(forall([x:int], x * 0 = 0), _),
    z3_declarations(Ds),
    assertion(memberchk((x/0):'Bool', Ds)),
    assertion(z3_is_implied(x)).

test(type_error_in_body) :-
    z3_reset,
    z3_push(forall([x:int], x and p), R),
    assertion(R == l_type_error).

% A function defined by a quantifier has an else value that depends on its arguments: it comes back
% as a lambda. (z3_model/1 used to fail here.)
test(model_of_defined_function) :-
    z3_reset,
    z3_push(forall([a:int, b:int], g(a, b) = a - b)),
    z3_model(M),
    assertion(M.functions = [(g/2 = else) = lambda(['x!0':int, 'x!1':int], _)]).

:- end_tests(z3pl_quantifiers).

% IEEE floating point through z3.pl's type inference.

:- begin_tests(z3pl_floating_point, [setup(reset_globals), cleanup(free_globals)]).

test(solve) :-
    z3_push(fp_add(rne, x:float32, fp_value(0.1, float32)) = fp_value(0.3, float32)),
    z3_model(M),
    memberchk(x = fp_value(V, float32), M.constants),
    assertion(abs(V - 0.2) < 1.0e-7).

test(sorts_inferred) :-
    z3_push(fp_lt(fp_add(m, x:float64, y), fp_value(1, float64))),
    z3_declarations(Ds0),
    msort(Ds0, Ds),
    assertion(Ds == [(m/0):roundingmode, (x/0):float64, (y/0):float64]).

% float32 and fp(8, 24) are the same sort.
test(alias) :-
    z3_push(x:float32 = y),
    z3_push(y:fp(8, 24) = fp_value(1.5, float32), Status),
    assertion(Status == l_true).

test(not_associative) :-
    assertion(\+ z3_is_implied(fp_add(rne, fp_add(rne, a:float16, b:float16), c:float16)
                               = fp_add(rne, a, fp_add(rne, b, c)))).

test(model_value_round_trip) :-
    z3_push(fp_is_subnormal(x:float64)),
    z3_model(M),
    memberchk(x = V, M.constants),
    z3_reset,
    z3_push(y:float64 = V),
    assertion(z3_is_implied(fp_is_subnormal(y))).

test(arithmetic_is_type_error) :-
    z3_push((x:float32) + 1 > 2, Status),
    assertion(Status == l_type_error).

test(float_sort_removed, [throws(error(domain_error(sort, float), _))]) :-
    z3_push(x:float > 1.0).

test(quantified) :-
    assertion(z3_is_implied(forall([z:float32], implies(not(fp_is_nan(z)), fp_leq(z, fp_abs(z)))))).

test(unsat_core) :-
    z3_unsat_core([fp_is_nan(x:float32), y:int > 0, fp_eq(x, x)], Core),
    assertion(Core == [fp_is_nan(x:float32), fp_eq(x, x)]).

test(arrays_of_floats) :-
    z3_push(select(a:array(int, float32), 0) = fp_value(2.5, float32)),
    z3_model(M),
    memberchk(a = A, M.constants),
    z3_reset,
    z3_push(b:array(int, float32) = A),
    assertion(z3_is_implied(fp_eq(select(b, 0), fp_value(2.5, float32)))).

% Models with conversions include Z3's function for their unspecified results (such as fp_to_sbv
% of NaN), whose else value depends on its arguments.
test(model_with_conversion) :-
    z3_push(b = fp_to_sbv(rtz, x:float32, 8)),
    z3_model(M),
    memberchk(b = _, M.constants),
    assertion(is_list(M.functions)).

:- end_tests(z3pl_floating_point).


:- begin_tests(enums).

test(enums_basic, [setup(reset_globals), cleanup(free_globals),
                   true(Z == [x=banana])
                  ]) :-
    z3_declare_enum(fruit, [apple, banana, pear]),
    z3_push(x:fruit <> pear),
    z3_is_implied(or(x = banana, x = apple)),
    z3_push(x <> apple),
    z3_model(M),
    Z = M.constants.

test(enum_declarations, [setup(reset_globals), cleanup(free_globals),
                          true(DeclSorted == [(black/0):color, (white/0):color])
                        ]) :-
    z3_declare_enum(color, [black, white]),
    z3_enum_declarations(Declarations),
    sort(Declarations, DeclSorted),
    get_global_handle(H),
    z3_enum_declarations_assoc(H, Map),
    assertion(get_assoc(black/0, Map, color)),
    true.

:- end_tests(enums).

:- include(z3_unit_tests).
