%%% -*- Mode: Prolog; Module: z3; -*-.

% The user-visible functions rely on an implicit solver, pushed and popped automatically, and a backtrackable type map:

:- module(z3, [
              solver_scopes/1,         % +Num_scopes, starting at 0
              z3_check/1,              % +Status Returns status of global solver: l_true, l_false, l_undet
              z3_check_and_print/1,    % +Status Returns status, prints model if possible
              z3_declarations/1,       % -Declarations  Get declarations so far, or those used in the previous query (reset on a new push).
              z3_declare_enum/2,       % +EnumName, +EnumValues. Not backtrackable.
              z3_enum_declarations/1,
              z3_eval/2,               % +Expression,-Result  Evaluates Expression in a current model, if the current solver is SAT.
              z3_eval/3,               % z3_eval, with boolean completion flag
              z3_is_consistent/1,      % +Formula  Succeeds if Formula is consistent with current solver/context. Fails if l_undet.
              z3_is_implied/1,         % +Formula  Succeeds if Formula is implied by current solver/context. Fails if l_undet.
              z3_model/1,              % +ModelTerm  Gets a model if possible. Fails if not l_sat.
              z3_model_assoc/1,        % +ModelAssocTerm  A model that uses assoc lists (less readable).
              z3_push/1,               % +Formula   Pushes the formula, fails if status is l_false.
              z3_push/2,               % +Formula, +Status  Attempts to push the formula, returns status
              z3_push_and_print/1,     % +Formula   Convenience
              z3_push_and_print/2,     % +Formula, +Status  Convenience
              z3_reset/0,              % resets everything, use sparingly
              free_globals/0,

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

For incrementality, this module maintains a global_handle, where the push and pops happen.
So even though it is a single Z3 C object, kept in a non-backtrackable Prolog variable, it is meant to works as a backtrackable one.

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
                  mappable_symbol/1
              ]).

:- use_module(z3_utils, [
                  ground_version/3,
                  remove_type_annotations/2,
                  reset_var_counts/0,
                  valid_status_list/1,
                  z3_declare/3,            % +Handle, +Formula,+Type    Declares Formula to have Type.
                  z3_declare_types_for_symbols/3,
                  z3_enum_declarations_assoc/2,
                  expand/2
                  ]
             ).

:- use_module(utils, [repeat_string/3,
                      pair_list_to_assoc/2
                     ]).

:- use_module(library(assoc)).
:- use_module(library(ordsets)).

:- use_module(z3_swi_foreign, [
                  z3_assert/2,
                  z3_declarations/2,
                  z3_declarations_string/2,
                  z3_declare_enum/3,
                  z3_declare_function/3,
                  z3_enum_declarations/2,
                  z3_enums_string/2,
                  z3_free_handle/1,
                  z3_free_model/2,
                  z3_get_model/2,
                  z3_model_eval/5,
                  z3_model_map/2,
                  z3_new_handle/1,
                  z3_reset_declarations/1,
                  z3_check/2,
                  z3_check_and_print/2,
                  z3_solver_pop/3,
                  z3_solver_push/2,
                  z3_solver_scopes/2
              ]).

% :- initialization(new_global_handle(_)).

free_handle :-
    (nb_current(global_handle, H) ->
         (
             print_message(informational, z3_message("Freeing old z3.pl handle")),
             z3_free_handle(H)
         )
    ;
    true),
    nb_delete(global_handle).


%! Resets the entire Z3 context. All declarations, including enums, are cleared.
%  Old models and solvers are invalidated.
z3_reset :-
    %% assertion(b_getval(solver_depth, 0)), %% test cleanup violates this
    free_handle,
    assertion(\+ get_global_handle(_)),
    new_global_handle(_).

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


%! Resets all declarations and solver, including enums:
reset_globals :-
    new_global_handle(_),
    reset_var_counts,
    initialize_type_inference_map.

z3_declare_enum(N,V) :- get_global_handle(H),
                        z3_declare_enum(H,N,V).

z3_enum_declarations(D) :- get_global_handle(H),
                           z3_enum_declarations(H, D).

z3_declarations(D) :- get_global_handle(H),
                      z3_declarations(H, D).

%%%%%%%%%%%%%%%%%%%%% Attribute variables %%%%%%%%%%%%%%%%%%%%%%%

attribute_goals(V) :- get_attr(V, z3, Attr),
                      z3_push(==(V, Attr), R),
                      \+ R = l_false.

%% Worth keeping an inverse map of "fake Z3 constants" to Prolog vars? Might need it for eval...
attr_unify_hook(Attr, Var) :- get_attr(Var, z3, Other), !,
                              report(informational, "Running hook for %w", [Other]),
                              z3_push(==(Attr, Other), R),
                              \+ R = l_false.
attr_unify_hook(Attr, Var) :- var(Var), !,
                              add_attribute(Var, Attr).
attr_unify_hook(Attr, Formula) :-
    %% report(informational, status("Hook got", Attr, Formula)),
    z3_push(==(Attr, Formula), R), \+ (R = l_false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% should only be called at the top-most level:

new_global_handle(Handle) :-
    print_message(informational, z3_message("Making new z3.pl handle")),
    free_handle,
    z3_new_handle(Handle),
    nb_setval(global_handle, Handle),
    nb_setval(solver_depth, 0),
    print_message(informational, z3_message("Made new z3.pl handle")).

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
solver_scopes(N) :- resolve_solver_depth(_), raw_solver_scopes(N).

% should not be used directly. Types in Formula could clash with previously defined types,
% so should use z3_push. Also the matter of push and pop.
internal_assert_and_check(Solver, Formula, Status) :-
    z3_assert(Solver, Formula),
    z3_check(Solver, Status).

z3_check(Status) :-
    check_status_arg(Status),
    get_global_handle(S),
    z3_check(S, Status).

z3_check_and_print(Status) :-
    check_status_arg(Status),
    get_global_handle(Solver),
    z3_check_and_print(Solver, Status).


%! z3_model(-Model)
%  Returns a model for the solver at the current depth, if z3_check succeeds.
%  Note that Z3 can return "uncertain" models if the status is l_undef.
z3_model(Model) :-
    resolve_solver_depth(_),
    z3_check(Status),
    member(Status, [l_true, l_undef]), !,
    get_global_handle(H),
    z3_model_map(H, Model).

%%  Next: share with stateful_repl.pl
z3_model_assoc(Model) :-
    z3_model(ModelLists),
    pair_list_to_assoc(ModelLists.constants, CA),
    pair_list_to_assoc(ModelLists.functions, FA),
    Model = model{constants:CA, functions:FA}.

check_status_arg(Status) :- valid_status_list(L),
                            must_be((var; oneof(L)), Status).

%% We now use backtrackable types in Prolog, resetting declarations at the first push.
%% Note that type declarations in Z3 can't be pushed and popped.
%% We could allow different types on different branches if new declarations overwrite old ones without error.

%% Note that z3_push(false, R) will still push "false" onto the solver.

z3_push(Foriginal, Status) :-
    check_status_arg(Status),
    (get_global_handle(H) -> true; new_global_handle(H)),
    expand(Foriginal, F),
    (b_getval(solver_depth, 0) ->
         z3_reset_declarations(H), %% does not clear enums
         z3_enum_declarations_assoc(H, EnumMap),
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
             internal_assert_and_check(Solver, FG_notypes, Status)
         )
    ;  (
        Status = l_type_error,
        get_type_inference_map_list(L),
        report(error, "Type error in term: %w. Type map was %w", [FG, L])
    )
    ).


%% z3_push/1 fails if solver reports inconsistency or type error.
%% l_type_error is the only one that does not push onto the solver.

z3_push(F) :- z3_push(F, R), (R == l_true ; R == l_undef), !.

solve(L, M) :- maplist(z3_push, L), z3_model(M).

z3_eval(Expression, Completion, Result) :-
    \+ is_list(Expression), !,
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

z3_eval(Expression, Result) :- z3_eval(Expression, false, Result).

%% Map eval on a list:
z3_eval_list(L, Completion, Result) :- must_be(list, L),
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
                          add_attribute(X, T).



/*
internal_assert_and_check_list(Solver, List, Status) :-
    Conj =.. [and | List],
    internal_assert_and_check(Solver, Conj, Status).
*/

z3_push_and_print(F,R) :- z3_push(F,R), z3_check_and_print(R1), assertion(R == R1).

z3_push_and_print(F) :- z3_push_and_print(F, l_true).

%% succeeds if F is consistent with the current context. Fails if l_undef.
z3_is_consistent(F) :- z3_push(F, l_true), popn(1).

%% to handle type errors correctly, need to distiguish failure-by-type-error from failure-by-inconsistency:
z3_is_implied(F) :- z3_push(not(F), Status),
                    (Status == l_true -> (popn(1) , fail)
                    ;
                    (Status == l_undef -> (popn(1) , fail)
                    ;
                    (Status == l_type_error -> fail
                    ;
                    (
                        assertion(Status == l_false),
                        popn(1)
                    )))).

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
    z3_model_assoc(M),
    get_assoc(x, M.constants, 3/5).

:- end_tests(large_numbers).


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
