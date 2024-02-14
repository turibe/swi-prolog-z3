%%% -*- Mode: Prolog; Module: z3; -*-

/** <module> Prolog documentation processor

This module builds on the basic functionality of z3_swi_foreign.pl to provide:

- Typechecking and declaring Z3 variables and functions
- Attributed variables
- pushing and popping assertions on the solver as we assert and backtrack

For incrementality, this module maintains a global_solver, where the push and pops happen.
So even though it is a single Z3 C object, kept in a non-backtrackable Prolog variable, it is meant to works as a backtrackable one.

type_inference_global_backtrackable does keep a --- backtrackable --- type map.

@author Tomas Uribe
@license MIT
*/


% All of the user-visible functions rely on an implicit solver, pushed accordingly, and a backtrackable type map:
:- module(z3, [
              solver_scopes/1,         % +Num_scopes, starting at 0
              z3_check/1,              % +Status Returns status of global solver: l_true, l_false, l_undet
              z3_check_and_print/1,    % +Status Returns status, prints model if possible
              z3_declare/2,            % +Formula,+Type    Declares Formula to have Type.
              z3_eval/2,               % +Expression,-Result  Evals Expression in a current model, if the current solver is SAT.
              z3_is_consistent/1,      % +Formula  Succeeds if Formula is consistent with current solver/context. Fails if l_undet.
              z3_is_implied/1,         % +Formula  Succeeds if Formula is implied by current solver/context. Fails if l_undet.
              z3_model/1,              % +ModelTerm  Gets a model if possible. Fails if not l_sat.
              z3_model_assoc/1,        % +ModelAssocTerm  A model that uses assoc lists (less readable).
              z3_push/1,               % +Formula   Pushes the formula, fails if status is l_false.
              z3_push/2,               % +Formula,+Status  Attempts to push the formula, returns status
              z3_push_and_print/1,     % +Formula   Convenience
              z3_push_and_print/2,     % +Formula,+Status  Convenience
              print_declarations/0,    % print declarations so far, or those used in the previous query (reset on a new push).
              
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>),  % different-than
              op(739, xfy, <=>), % iff
              op(199, xfy, :)
              % {}/1, % clashes with other CLP libraries
              ]).

:- use_module(type_inference_global_backtrackable, [
                  assert_type/2,
                  get_map/1 as get_type_inference_map,
                  get_map_list/1 as get_type_inference_map_list
              ]).

:- use_module(library(assoc)).
:- use_module(library(ordsets)).

:- use_module(z3_swi_foreign, [
                  z3_assert/3,
                  z3_declarations_string/2,
                  z3_declaration_map_size/2,
                  z3_free_model/1,
                  z3_free_solver/1,
                  z3_declare_function/3,
                  z3_make_solver/1,
                  z3_model_eval/5,
                  z3_model_map_for_solver/2,
                  z3_make_declaration_map/1,
                  z3_reset_declaration_map/1,
                  z3_solver_check/2,
                  z3_solver_check_and_print/2,
                  z3_solver_get_model/2,
                  z3_solver_pop/3,
                  z3_solver_push/2,
                  z3_solver_scopes/2
              ]).


reset_z3_declaration_map :- nb_current(global_decl_map, M) -> z3_reset_declaration_map(M)
                                 ;
                                 ( z3_make_declaration_map(M),
                                   nb_setval(global_decl_map, M)
                                 ).

% The declaration map that lives in Z3
get_z3_declaration_map(M) :- nb_getval(global_decl_map, M).


% if solver push/pop and backtrackable type inference work as they should,
% end-users don't need to call this:
z3_reset_declarations :- get_z3_declaration_map(M), z3_reset_declaration_map(M).

%% have a global variable, backtrackable, with the depth level.
%% before the assert, check that variable, and pop the solver as many times as needed.

:- initialization(reset_globals).

%% indent according to solver pushes:
report(T) :- indent, print(T), nl, flush_output.

indent :- assert_depth(N),
          forall(between(1, N, _X), (print(---), print(N))).

reset_globals :-
    reset_z3_declaration_map,
    reset_global_solver,
    reset_var_counts,
    type_inference:initialize.

reset_var_counts :- nb_setval(varcount, 0).

inc_var_count(X) :- nb_getval(varcount, X),
                    New is X + 1,
                    nb_setval(varcount, New).

%%%%% Attribute (Prolog) variables %%%%%%%%%%

add_attribute(V, Attr) :- var(V),
                          get_attr(V, z3, Attr), !, %  equality should already be asserted
                          true.
add_attribute(V, Attr) :- var(V),
                          inc_var_count(Count),
                          atom_concat(v_, Count, Attr),
                          put_attr(V, z3, Attr).

attribute_goals(V) :- get_attr(V, z3, Attr),
                      z3_push(==(V, Attr), R),
                      \+ R = l_false.

%% Worth keeping an inverse map of "fake Z3 constants" to Prolog vars? Might need it for eval...
attr_unify_hook(Attr, Var) :- get_attr(Var, z3, Other), !,
                              report(status("Running hook for", Other)),
                              z3_push(==(Attr, Other), R),
                              \+ R = l_false.
attr_unify_hook(Attr, Var) :- var(Var), !,
                              add_attribute(Var, Attr).
attr_unify_hook(Attr, Formula) :-
    %% report(status("Hook got", Attr, Formula)),
    z3_push(==(Attr, Formula), R), \+ (R = l_false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% should only be called at the top-most level:
reset_global_solver :-
    (get_global_solver(Old) -> z3_free_solver(Old) ; true),
    z3_make_solver(S),
    nb_setval(global_solver, S),
    nb_setval(solver_depth, 0).

get_global_solver(S) :- nb_current(global_solver, S).

assert_depth(N) :- b_getval(solver_depth, N).


%% we should only use push_solver to get the solver.
%% and it should always be called before an assert, if we want it to be retractable.
%% So, hide push_solver, expose asserts.

push_solver(S) :- get_global_solver(S),
                  resolve_solver_depth(X),
                  New is X + 1,
                  b_setval(solver_depth, New),
                  z3_solver_push(S, _D).


raw_solver_scopes(N) :- get_global_solver(S), z3_solver_scopes(S,N).

%% Pops the Z3 context to match the PL solver_depth:
resolve_solver_depth(X) :- b_getval(solver_depth, X),
                           raw_solver_scopes(N),
                           resolve_solver_depth(X, N).


resolve_solver_depth(X, Scopes) :- X >= Scopes,
                                       % report(status("scopes OK", Scopes, X)),
                                       !.
resolve_solver_depth(X, Scopes) :- X < Scopes,
                                   % report(status("need to pop", Scopes, X)),
                                   Numpops is Scopes - X,
                                   popn(Numpops).

popn(Numpops) :- get_global_solver(S),
                 z3_solver_pop(S, Numpops, _) -> true ; report("error popping Z3 solver\n").

%% user-visible:
solver_scopes(N) :- resolve_solver_depth(_), raw_solver_scopes(N).

% should not be used directly. Types in Formula could clash with previously defined types,
% so should use z3_push. Also the matter of push and pop.
internal_assert_and_check(Solver, Formula, Status) :-
    get_z3_declaration_map(Map),
    z3_assert(Map, Solver, Formula),
    z3_solver_check(Solver, Status).

z3_check(Status) :-
    check_status_arg(Status),
    get_global_solver(S),
    z3_solver_check(S, Status).

z3_check_and_print(Status) :-
    check_status_arg(Status),
    get_global_solver(Solver),
    z3_swi_foreign:z3_solver_check_and_print(Solver, Status).
    

% returns a model for the current solver, if check succeeds:
z3_model(Model) :-
    resolve_solver_depth(_),
    z3_check(l_true),
    get_global_solver(S),
    z3_model_map_for_solver(S, Model).

z3_model_assoc(Model) :-
    z3_model(ModelLists),
    list_to_assoc(ModelLists.constants, CA),
    list_to_assoc(ModelLists.functions, FA),
    Model = model{constants:CA, functions:FA}.


% We now allow overloading by arity.
% Grounds any variables in X, and returns the symbols it finds, using f/N for arities bigger than 1.
ground_version(X, Attr, [Attr]) :- var(X), !, add_attribute(X, Attr).
ground_version(X, X, S) :- number(X), !, ord_empty(S).
ground_version(X, X, [X]) :- atom(X), !, true.
ground_version(C, XG:T, Result) :- compound(C), C = X:T, !,
                                   (ground(T) -> true ; type_error(ground, T)),
                                   ground_version(X, XG, Result).
ground_version(X, G, Result) :- compound(X),
                                functor(X, F, Arity),
                                X =.. [F|Rest],
                                ground_list(Rest, Grest, R),
                                G =.. [F|Grest],
                                ord_add_element(R, F/Arity, Result).


ground_list([], [], S) :- ord_empty(S).
ground_list([F|Rest], [FG|Grest], Result) :- ground_version(F, FG, GFG), ground_list(Rest, Grest, Arest), ord_union(GFG, Arest, Result).

valid_status_list([l_true, l_false, l_undef]).
valid_status(X) :- valid_status_list(L), member(X, L).


check_status_arg(Status) :- var(Status), !, true.
check_status_arg(Status) :- nonvar(Status),
                            (valid_status(Status) -> true ; (
                                valid_status_list(L),
                                domain_error(L, Status)
                            )), !.


%% We now use backtrackable types, resetting declarations at the first push.
%% Note that type declarations in Z3 can't be pushed and popped.

%% We could allow different types on different branches if new declarations overwrite old ones without error.

z3_push(F, Status) :-
    check_status_arg(Status),
    (b_getval(solver_depth, 0) -> z3_reset_declarations ; true),
    get_type_inference_map(OldAssoc),
    %% report(status("asserting", F)),
    ground_version(F, FG, Symbols),
    (type_inference_global_backtrackable:assert_type(FG, bool) -> true ;
     (report(type_error(FG)),
      get_type_inference_map_list(L),
      report(map(L)),
      fail)),
    get_type_inference_map(Assoc),
    %% we only need to declare new symbols:
    exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
    %% writeln(compare(Symbols, NewSymbols)),
    declare_z3_types_for_symbols(NewSymbols, Assoc),
    push_solver(Solver),
    internal_assert_and_check(Solver, FG, Status).


%% z3_push/1 fails if solver reports inconsistency:

z3_push(F) :- z3_push(F, R), \+ (R == l_false).

%% goes through a list of symbols and declares them in Z3, using z3_declare
declare_z3_types_for_symbols([], _M).
declare_z3_types_for_symbols([X|Rest], M) :- (get_assoc(X, M, Def) -> z3_declare(X, Def) ; true),
                                 declare_z3_types_for_symbols(Rest, M).


print_declarations :- get_z3_declaration_map(M), z3_declarations_string(M, S), current_output(Out), write(Out, S).

z3_eval(Expression, Completion, Result) :-  \+ is_list(Expression),
                                get_global_solver(S),
                                get_z3_declaration_map(Map),
                                z3_solver_check(S, Status),
                                Status == l_true,
                                replace_var_attributes(Expression, E1),
                                setup_call_cleanup(
                                    z3_solver_get_model(S, Model),
                                    z3_swi_foreign:z3_model_eval(Map, Model, E1, Completion, Result),
                                    z3_free_model(Model)
                                ).

z3_eval(Expression, Result) :- z3_eval(Expression, false, Result).

%% Map eval on a list:
z3_eval([], []).
z3_eval([X|Rest],[EX|Erest]) :-
        z3_eval(X, EX),
        z3_eval(Rest, Erest). % Cuold make more efficient, do only one check and one get_model.


%% A little inefficient for big terms, might be better to do in the C code eval:
replace_var_attributes(X, A) :- var(X), get_attr(X, z3, A), !, true.
replace_var_attributes(X, X) :- \+ compound(X), !, true.
replace_var_attributes(X, R) :- compound(X),
                                mapargs(replace_var_attributes, X, R).


%% NOTES: If we declare uninterpreted types, say, for a=b, later on assert a=1, then the type for a would change.
%% But Z3 does not let us change types, so this case is not handled. (Ideally, we would equate them, adding "uninterpreted = int").

get_term_for_var(X, T) :- var(X),
                          add_attribute(X, T).


%% z3_declare updates the internal (C) Z3 decl map:

z3_declare(F:T) :- z3_declare(F, T). %% take care of explicit types
z3_declare(F, T) :- var(F), !,
                    add_attribute(F, Attr),
                    z3_declare(Attr, T).
z3_declare(F, int) :- integer(F), !, true.
z3_declare(F, real) :- float(F), !, true.
z3_declare(F, T) :- atom(T), !,
                    get_z3_declaration_map(M),
                    z3_declare_function(M, F, T).
z3_declare(F, T) :- var(T), !,
                    T = uninterpreted,
                    get_z3_declaration_map(M),
                    z3_declare_function(M, F, T).
z3_declare(F, lambda(Arglist, Range)) :- (var(F) -> type_error(nonvar, F) ; true), !,
                                         F = F1/N,
                                         length(Arglist, Len),
                                         assertion(N == Len),
                                         Fapp =.. [F1|Arglist],
                                         (var(Range) -> Range = uninterpreted ; true), !,
                                         get_z3_declaration_map(M),
                                         z3_declare_function(M, Fapp, Range).


%% Not used --- not incremental, declares everything in the map:
%% %% typecheck_and_declare/2, % +Formula,-Assoc  : Typechecks Formula, declares types, and returns new Assoc
%% typecheck_and_declare(Formulas, Assoc) :-
%%     assert_formula_list_types(Formulas), !, %% updates the global (backtrackable) type map
%%     get_type_inference_map(Assoc),
%%     assoc_to_list(Assoc, L),
%%     declare_type_list(L).                   %% updates the Z3 (C) internal map

%% %% declare_type_list/1,     % +List of Term-Type or Term:Type pairs
%% declare_type_list([]).
%% declare_type_list([A-B|R]) :- z3_declare(A, B), declare_type_list(R).
%% declare_type_list([A:B|R]) :- z3_declare(A, B), declare_type_list(R).


internal_assert_and_check_list(Solver, List, Status) :-
    Conj =.. [and | List],
    internal_assert_and_check(Solver, Conj, Status).


z3_push_and_print(F,R) :- z3_push(F,R), z3_check_and_print(R1), assertion(R == R1).

z3_push_and_print(F) :- z3_push_and_print(F, l_true).

%% succeeds if F is consistent with the current context. Fails if l_undef.
z3_is_consistent(F) :- setup_call_cleanup(true,
                                          z3_push(F, l_true),
                                          popn(1)
                                         ).

z3_is_implied(F) :- \+ z3_is_consistent(not(F)).

{}(X) :- z3_push(X).


%%%%%%%%%%%%%%%%%%%%%%%%%% unit tests %%%%%%%%%%%%%%%%%


:- begin_tests(push_assert_tests).

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

test(typetest, [true(A-F == int-lambda([foobarsort], int)) , nondet ] ) :-
    test_formulas(Formulas),
    type_inference_global_backtrackable:assert_formula_list_types(Formulas),
    get_type_inference_map(Map),
    get_assoc(a, Map, A),
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
    z3_push(atleast(a:bool, b:bool, c:bool, 2), R), z3_push(a, R1), z3_push(not(b), R2), z3_push(not(c), R3),
    R = l_true,
    R1 = l_true,
    R2 = l_true,
    R3 = l_false.

test(consistent) :-
    z3_push(and(a:int>b, b>c, c>d)), \+ z3_is_consistent(d>a),
    z3_is_consistent(a > d),
    z3_push(a > d).

test(implied) :-
    z3_push(and(a:int>b,b>c,c>d)), z3_is_implied(a>d).

test(boolean) :-
    z3_push(or(and(a:bool, b:bool), not(c:bool))),
    z3_push(c:bool),
    z3_is_implied(a).

test(eval, [true(R == 6)]) :-
    z3_push(a = 2),
    z3_push(b = 3),
    z3_eval(a * b, R).


%% todo: undef, as in:
%% z3_push(power(a:real,b:int) = c, R), z3_push(c=2.0, R1), z3_push(a=2.0, R2).

%% to see how the model changes:
%% z3:z3_push(b:int>c,R), z3:z3_push(and(a>d:int,b>e:int),R1), z3_push(f > b), z3_model(M), z3_is_consistent(f < a), z3_model(M1), z3_push(f > a), z3_model(M2).
%% or z3_push_and_print(a > 1), z3_push_and_print(b > 2), z3_push_and_print(a > b), solver_scopes(N).

test(scopes, [true(N1 == 1), true(N2==2)] ) :-
    solver_scopes(0),
    z3_push(a:int=14), solver_scopes(N1), z3_push(b:int=a-5), solver_scopes(N2).

:- end_tests(push_assert_tests).


:- begin_tests(attribute_tests).

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
    z3_push(X=14), z3_push(Y=X-5), z3_push(a = X-1), z3_push(b = Y*Y), z3_model(M),
    assertion(member(a-13, M.constants)),
    assertion(member(b-81, M.constants)).

:- end_tests(attribute_tests).

:- begin_tests(boolean_tests).

test(bool_plus) :-
    z3_push((a:real) + (b:bool) = 3.0), z3_push(b), z3_model(M),
    M.constants == [b-true, a-2].

test(bool_times) :-
    z3_push((a:real) * (b:bool) = 0.0), z3_push(a = 3.2), z3_model(M),
    assertion(M.constants == [b-false, a-16/5]).

test(more_arith) :-
    z3_push(a:bool + b:real = 1.0), z3_model(M1), z3_push(b < 1), z3_model(M2),    
    assertion(M1.constants == [a-false, b-1]),
    assertion(M2.constants == [a-true, b-0]).

test(bool_or) :-
    z3_push(((a;b))), z3_push(not(b)), z3_model(M),
    assertion(M.constants == [a-true, b-false]).

test(bool_and) :-
    z3_push((a,b)), z3_model(M),
    assertion(M.constants == [a-true, b-true]).

test(bool_andor, [fail]) :-
    z3_push((a,b)), z3_push(((not(a), not(b)))).

test(bool_implies) :-
    z3_push(a->b), z3_model(M),
    assertion(M.constants = [a-false]).

test(bool_iff) :-
    z3_push(a<=>b), z3_push(a), z3_model(M),
    assertion(M.constants = [a-true, b-true]).

:- end_tests(boolean_tests).


:- include(z3_unit_tests).
