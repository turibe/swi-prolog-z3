%%% -*- Mode: Prolog; Module: z3; -*-

% This module builds on the basic functionality of z3_swi_foreign.pl to provide:
%
% - Typechecking and declaring Z3 variables and functions
% - Attributed variables
% - pushing assertions

:- module(z3, [
              typecheck_and_declare/2,
              declare_type_list/1,
              z3_declare/2,
              z3_push/2,
              z3_push/1,
              z3_print_status/1,
              z3_push_and_print/2,
              z3_push_and_print/1,
              z3_eval/2,
              z3_is_implied/1,
              z3_implies/1,
              z3_entails/1,
              z3_is_consistent/1,
              get_global_solver/1,
              z3_get_model/1,
              z3_model_eval/2,
	      z3_model_eval/3,
              z3_check_and_print/1,
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>)
              % {}/1,
              ]).

:- use_module(type_inference_global, [
                  assert_formula_list_types/1,
                  assert_type/2,
                  get_map/1
              ]).

:- use_module(library(assoc)). % use dicts instead? Both can't handle vars as keys properly.
:- use_module(library(ordsets)).

%% :- load_foreign_library(z3_swi_foreign).
:- use_module(z3_swi_foreign).

:- use_module(quickexplain).

%% have a global variable, backtrackable, with the depth level.
%% before the assert, check that variable, and pop the solver as many times as needed.

:- initialization(reset_globals).

%% TODO: indent according to solver pushes?
report(T) :- indent, print(T), nl, flush_output.

indent :- assert_depth(N),
          forall(between(1, N, _X), (print(---), print(N))).

reset_globals :-
    reset_global_solver,
    reset_var_counts,
    z3_reset_declarations,
    type_inference:initialize.

reset_var_counts :- nb_setval(varcount, 0).

inc_var_count(X) :- nb_getval(varcount, X),
                    New is X + 1,
                    nb_setval(varcount, New).

add_attribute(V, Attr) :- var(V),
                          get_attr(V, z3, Attr), !, %  equality should already be asserted
                          true.
add_attribute(V, Attr) :- var(V),
                          inc_var_count(Count),
                          atom_concat(v_, Count, Attr),
                          put_attr(V, z3, Attr).
                          % z3_push(==(V, Attr), R), % need push, pop, etc. // FIXME: we are declaring a lot of things over and over
                          % \+ R = l_false.

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


%% should only be called at the top-most level:
reset_global_solver :-
    z3_mk_solver(S),
    nb_setval(global_solver, S),
    nb_setval(solver_depth, 0).

get_global_solver(S) :- nb_getval(global_solver, S).

assert_depth(N) :- b_getval(solver_depth, N).

%% TODO:
%% we should only use mypush to get the solver.
%% and it should always be called before an assert, if we want it to be retractable.
%% So, hide mypush, expose asserts.
mypush(S) :- get_global_solver(S),
             resolve_solver_depth(S, X),
             New is X + 1,
             b_setval(solver_depth, New),
             z3_solver_push(S, _D).

resolve_solver_depth(Solver, X) :- b_getval(solver_depth, X),
                                  z3_solver_scopes(Solver, N),
                                  resolve_solver_depth(Solver, X, N).

resolve_solver_depth(_S, X, Scopes) :- X >= Scopes,
                                       % report(status("scopes OK", Scopes, X)),
                                       !.
resolve_solver_depth(S, X, Scopes) :- X < Scopes,
                                      % report(status("need to pop", Scopes, X)),
                                      Numpops is Scopes - X,
                                      popn(S, Numpops).

popn(S, Numpops) :- z3_solver_pop(S, Numpops, _) -> true ; report("error popping Z3 solver\n").


% should not be used directly. Types in Formula could clash with previously defined types,
% so should use z3_push. Also the matter of push and pop.
internal_assert_and_check(Solver, Formula, Status) :-
    z3_assert(Solver, Formula),
    z3_solver_check(Solver, Status).


% TODO: we don't allow overloading by arity. If we keep track of arity here and in type map, can do it.
ground_version(X, Attr, [Attr]) :- var(X), !, add_attribute(X, Attr).
ground_version(X, X, []) :- number(X), !, true.
ground_version(X, X, [X]) :- atom(X), !, true.
ground_version(C, XG:T, Result) :- compound(C), C = X:T, !,
    (ground(T) -> true ; type_error(ground, T)),
    ground_version(X, XG, Result).
ground_version(X, G, Result) :- X =.. [F|Rest],
                        ground_list(Rest, Grest, R),
                        G =.. [F|Grest],
                        ord_add_element(R, F, Result).


ground_list([F|Rest], [FG|Grest], Result) :- ground_version(F, FG, GFG), ground_list(Rest, Grest, Arest), ord_union(GFG, Arest, Result).
ground_list([], [], S) :- ord_empty(S).


%% We now use backtrackable types. Confusing that types remain but assertions don't.
%% or use a combination of both?
%% Problem is that type declarations in Z3 can't be popped.
%% on the other hand, new declarations over-write old ones... (we're keeping our own map there).
%% so if we make sure that the Z3 declarations are always the latest ones, we're OK.
%% But it is INEFFICIENT.

%% FIXME: assert_type should ignore builtins like "atleast", otherwise they can't be overloaded.
%% also ignore constants 1,2,3, ...

z3_push(F, Status) :-
    %% report(status("asserting", F)),
    ground_version(F, FG, Symbols),
    (type_inference_global:assert_type(FG, bool) -> true ;
     (report(type_error(FG)),
      type_inference_global:show_map(L),
      report(map(L)),
      fail)),
    get_map(Assoc),
    % assoc_to_list(Assoc, L),
    % declare_type_list(L), %% this declares the entire type list again
    % TODO: use only the ones in F?
    declare_types(Assoc, Symbols),
    mypush(Solver),
    internal_assert_and_check(Solver, FG, Status).

% z3_push fails if solver reports inconsistency
z3_push(F) :- z3_push(F, l_true).

% does not work:
% {X} :- z3_push{X}.

% maybe: implement with a forall? Only interested in side effect, no unification needed.

declare_types(M, [X|Rest]) :- (get_assoc(X, M, Def) -> z3_declare(X, Def) ; true), !,
                              declare_types(M, Rest).
declare_types(_M, []) :- true.

z3_print_status(Status) :- get_global_solver(Solver), z3_solver_check_and_print(Solver, Status).

z3_check_and_print(S) :- z3_print_status(S).

print_declarations :- z3_declarations_string(S), current_output(Out), write(Out, S).

z3_eval(Expression, Result) :-  \+ is_list(Expression),
                               get_global_solver(S),
                               z3_solver_check(S, Status),
                               Status == l_true, % TODO: investigate l_undef
                               z3_solver_get_model(S, Model),
                               z3_model_eval(Model, Expression, Result).

z3_eval([], []) :- !, true.
z3_eval([X|Rest],[EX|Erest]) :- z3_eval(X, EX), z3_eval(Rest, Erest). % FIXME: make more efficient, do only one check

z3_get_model(M) :- get_global_solver(S), z3_solver_get_model(S,M).
%% TODO/FIXME: replace variables by their attributes:
%% Example: z3_push(X=14), z3_push(Y=X-5), Y=9, get_attr(X,z3,A), z3_model_eval(A+1,R). (works)
%% vs. z3_push(X=14), z3_push(Y=X-5), Y=9, get_attr(X,z3,A), z3_model_eval(X+1,R). (doesn't work)
z3_model_eval(Expression, Result) :- z3_get_model(M), z3_model_eval(M, Expression, Result).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% lower level (used to be z3_wrapper.pl) %%%%%%

%% NOTES: If we declare uninterpreted types, say,  for a=b, later on assert a=1, then type for a would change.
%% But Z3 does not let us change types, so this case is not handled. (Ideally, we would equate them, adding "uninterpreted = int").

get_term_for_var(X, T) :- var(X),
                          add_attribute(X, T).

% z3_declare takes care of types:
z3_declare(F:T) :- z3_declare(F, T).

% TODO/QUESTION: do we need attributed variables at all? Guess so, if other solvers will connect to it.
% Old: If T is a var, the variable works as its own sort. % The z3_function_declaration code unifies it with an undef_sort_X atom.
% New: we unify it here.
z3_declare(F, T) :- var(F), !,
                    add_attribute(F, Attr),
                    z3_declare(Attr, T).
% z3_declare(F, T) :- var(F), \+ var(T), !,
%                    report(status("Cannot declare vars to have compound type", T)),
%                    fail.
z3_declare(F, int) :- integer(F), !, true.
z3_declare(F, real) :- float(F), !, true.
z3_declare(F, T) :- atom(T), \+ var(T), !, 
                    z3_function_declaration(F, T).
z3_declare(F, T) :- var(T), !, T = uninterpreted, z3_function_declaration(F, T).
z3_declare(F, lambda(Arglist, Range)) :- (var(F) -> type_error(nonvar, F) ; true), !,
                                         Fapp =.. [F|Arglist],
                                         (var(Range) -> Range = uninterpreted ; true), !,
                                         z3_function_declaration(Fapp, Range).

typecheck_and_declare(Formulas, Assoc) :-
    %% BUG: these don't work, they do not unify across the assoc.
    %% forall(gen_assoc(K, Assoc, Val), z3_declare(K, Val)).
    %% foreach(gen_assoc(K, Assoc, Val), z3_declare(K, Val)).
    assert_formula_list_types(Formulas), !, %% gets the latest map from global
    type_inference_global:get_map(Assoc),
    assoc_to_list(Assoc, L),
    declare_type_list(L).


declare_type_list([]) :- !, true.
declare_type_list([A-B|R]) :- z3_declare(A, B), declare_type_list(R).


internal_assert_and_check_list(Solver, List, Status) :-
    Conj =.. [and | List],
    internal_assert_and_check(Solver, Conj, Status).


z3_push_and_print(F,R) :- z3_push(F,R), z3_print_status(R).

z3_push_and_print(F) :- z3_push_and_print(F, _R).

z3_is_consistent(F) :- z3_push(F, l_true) -> (
                                                     get_global_solver(S),
                                                     popn(S,1),
                                                     true
                                                 ); (
                        get_global_solver(S),
                        popn(S,1),
                        false
                       ).
z3_is_implied(F) :- \+ z3_is_consistent(not(F)).

z3_entails(X) :- z3_is_implied(X).
z3_implies(X) :- z3_is_implied(X).

%% TODO: could go through all declarations,
%% call Z3_model_get_const_interp(), but that also returns a Z3_ast.
%% Looks like to get functions back, have to deal with Z3_func_interp objects.

{}(X) :- z3_push(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5

%%%%%%%%%%%%%%%%%%%%%%%%%% unit tests %%%%%%%%%%%%%%%%%


:- begin_tests(wrapper_tests).

test_test :- print("testing").

test_formulas(Formulas) :-
    Formulas = [foo(a) = b+c,
                foo(b) = 2,
                a = (b:int), %% int should remove choicepoint?
                b = a,
                d:int = f(e:foobarsort),
                foo(b) = c % this implies b = 0
               ] %  b = 2 %% TODO: get model out
               .

doit(Formulas, S, R) :-
    typecheck_and_declare(Formulas, _Assoc),
    Conjunction =.. [and | Formulas],
    z3_assert(S, Conjunction), %% makes a new solver
    z3_solver_check_and_print(S, R).

doit(R) :-
    test_formulas(Formulas),
    doit(Formulas, _Solver, R).

typetest(Formulas, R) :-
    assert_formula_list_types(Formulas),
    type_inference_global:get_map(Map),
    assoc_to_list(Map, R).

%% fix: choicepoint
test(typetest) :-
    test_formulas(Formulas),
    typetest(Formulas, _Assoc).

test(sat) :- reset_globals, doit(R), R = l_true.

test(nonsat) :-
    test_formulas(Formulas),
    % typetest(Formulas, _Assoc), % introduces choicepoint
    doit(Formulas, Solver, _R1),
    z3_assert(Solver, b=2),
    z3_solver_check_and_print(Solver, R2),
    R2 = l_false.

:- end_tests(wrapper_tests).

:- begin_tests(assert_tests).

% z3_push(y:real > 2, R0), z3_push_and_print(a:real=div(x, y), R), z3_push_and_print(a = div(b:real, 4.0), R1), z3_push_and_print(a >0.0, R2).
% z3_push_and_print(a:real=div(x, y), R), z3_push_and_print(a = div(b, 4.0), R1).

test(atmost0) :-
    z3_push(atmost(a:bool, b:bool, c:bool, 0), R), z3_push(a, R1),
    R = l_true,
    R1 = l_false.

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
    z3_push(and(a:int>b,b>c,c>d)), \+ z3_is_consistent(d>a).
test(implied) :-
    z3_push(and(a:int>b,b>c,c>d)), z3_is_implied(a>d).

%% todo: undef, as in:
%% z3_push(power(a:real,b:int) = c, R), z3_push(c=2.0, R1), z3_push(a=2.0, R2).

:- end_tests(assert_tests).


:- begin_tests(attribute_tests).

test(a1) :- % [nondet]
    z3_push(X>10, R), X = 12, R = l_true.

test(fail, [fail] ) :-
    z3_push(X:int>Y, _R),
    X = 10,
    Y = 14.


:- end_tests(attribute_tests).

