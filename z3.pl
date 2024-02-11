%%% -*- Mode: Prolog; Module: z3; -*-

% This module builds on the basic functionality of z3_swi_foreign.pl to provide:
%
% - Typechecking and declaring Z3 variables and functions
% - Attributed variables
% - pushing and popping assertions on the solver as we assert and backtrack
%
% For incrementality, this module maintains a global_solver, where the push and pops happen.
% So even though it is a single Z3 C object, kept in a non-backtrackable Prolog variable, it is meant to works as a backtrackable one.
%
% type_inference_global does keep a backtrackable type map.
%

% All the user-visible functions rely on an implicit solver, pushed accordingly, and a backtrackable type map:
:- module(z3, [
              declare_type_list/1,     % +List of Term-Type or Term:Type pairs
              solver_scopes/1,         % +Num_scopes, starting at 0
              typecheck_and_declare/2, % +Formula,-Assoc  : Typechecks Formula, declares types, and returns new Assoc
              z3_check/1,              % +Status Returns status of global solver: l_true, l_false, l_undet
              z3_check_and_print/1,    % +Status Returns status, prints model if possible
              z3_declare/2,            % +Formula,+Type    Declares Formula to have Type.
              z3_eval/2,               % +Expression,-Result  Evals Expression in a current model, if the current solver is SAT.
              z3_is_consistent/1,      % +Formula  Succeeds if Formula is consistent with current solver/context. Fails if l_undet.
              z3_is_implied/1,         % +Formula  Succeeds if Formula is implied by current solver/context. Fails if l_undet.
              z3_model_map/1,          % +ModelTerm  Gets a model if possible. Fails if not l_sat.
              z3_model_assoc/1,
              z3_push/1,               % +Formula   Pushes the formula, fails if status is l_false.
              z3_push/2,               % +Formula,+Status  Attempts to push the formula, returns status
              z3_push_and_print/1,     % +Formula   Convenience
              z3_push_and_print/2,     % +Formula,+Status  Convenience
              %% reset_globals/0,
              print_declarations/0,
              op(750, xfy, and), % =, >, etc. are 700
              op(751, xfy, or),
              op(740, xfy, <>)
              % {}/1, % clashes
              ]).

:- use_module(type_inference_global, [
                  assert_formula_list_types/1,
                  assert_type/2,
                  get_map/1
              ]).

:- use_module(library(assoc)). % use dicts instead? Both can't handle vars as keys properly.
:- use_module(library(ordsets)).

:- use_module(z3_swi_foreign, [
		  z3_assert/3,
		  z3_declarations_string/2,
                  z3_declaration_map_size/2,
		  z3_free_model/1,
		  z3_free_solver/1,
		  z3_function_declaration/3,
		  z3_make_solver/1,
		  z3_model_eval/4,
		  z3_model_map/2,
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


% gets a Prolog term representing a model for the given solver S:
z3_model_map_for_solver(S, Model) :-
    setup_call_cleanup(z3_solver_get_model(S,M),
                       z3_swi_foreign:z3_model_map(M, Model),
                       z3_free_model(M)
                      ).
    

% returns a model for the current solver, if check succeeds:
z3_model_map(Model) :-
    resolve_solver_depth(_),
    z3_check(l_true),
    get_global_solver(S),
    z3_model_map_for_solver(S, Model).

z3_model_assoc(Model) :-
    z3_model_map(ModelLists),
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
%% Problem is that type declarations in Z3 can't be popped.
%% on the other hand, new declarations could over-write old ones in Z3 (TODO)... (we're keeping our own map there).
%% so if we make sure that the Z3 declarations are always the latest ones, we're OK.

%% TODO: We could allow different types on different branches if new declarations overwrite old ones without error.

%% FIXME: assert_type should ignore builtins like "atleast", otherwise they can't be overloaded.
%% also ignore constants 1,2,3, ...

z3_push(F, Status) :-
    check_status_arg(Status),
    (b_getval(solver_depth, 0) -> z3_reset_declarations ; true),
    type_inference_global:get_map(OldAssoc),
    %% report(status("asserting", F)),
    ground_version(F, FG, Symbols),
    (type_inference_global:assert_type(FG, bool) -> true ;
     (report(type_error(FG)),
      type_inference_global:show_map(L),
      report(map(L)),
      fail)),
    type_inference_global:get_map(Assoc),
    %% we only need to declare new symbols:
    exclude(>>({OldAssoc}/[X], get_assoc(X, OldAssoc, _Y)), Symbols, NewSymbols),
    %% writeln(compare(Symbols, NewSymbols)),
    declare_types(NewSymbols, Assoc),
    push_solver(Solver),
    internal_assert_and_check(Solver, FG, Status).

%% z3_push/1 fails if solver reports inconsistency:
z3_push(F) :- z3_push(F, R), \+ (R == l_false).

% does not work:
% {X} :- z3_push{X}.


declare_types([], _M).
declare_types([X|Rest], M) :- (get_assoc(X, M, Def) -> z3_declare(X, Def) ; true), !,
                              declare_types(Rest, M).


print_declarations :- get_z3_declaration_map(M), z3_declarations_string(M, S), current_output(Out), write(Out, S).

z3_eval(Expression, Result) :-  \+ is_list(Expression),
                                get_global_solver(S),
                                get_z3_declaration_map(Map),
                                z3_solver_check(S, Status),
                                Status == l_true, % TODO: investigate l_undef
                                replace_var_attributes(Expression, E1),
                                setup_call_cleanup(
                                    z3_solver_get_model(S, Model),
                                    z3_swi_foreign:z3_model_eval(Map, Model, E1, Result),
                                    z3_free_model(Model)
                                ).

z3_eval([], []).
z3_eval([X|Rest],[EX|Erest]) :-
        z3_eval(X, EX),
        z3_eval(Rest, Erest). % FIXME: make more efficient, do only one check and one get model


%% A little inefficient for big terms, might be better to do in the C code eval:
replace_var_attributes(X, A) :- var(X), get_attr(X, z3, A), !, true.
replace_var_attributes(X, X) :- \+ compound(X), !, true.
replace_var_attributes(X, R) :- compound(X),
                                mapargs(replace_var_attributes, X, R).


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
% TODO: add tests.
z3_declare(F, T) :- var(F), !,
                    add_attribute(F, Attr),
                    z3_declare(Attr, T).
z3_declare(F, int) :- integer(F), !, true.
z3_declare(F, real) :- float(F), !, true.
z3_declare(F, T) :- atom(T), !,
                    get_z3_declaration_map(M),
                    z3_function_declaration(M, F, T).
z3_declare(F, T) :- var(T), !,
                    T = uninterpreted,
                    get_z3_declaration_map(M),
                    z3_function_declaration(M, F, T).
z3_declare(F, lambda(Arglist, Range)) :- (var(F) -> type_error(nonvar, F) ; true), !,
                                         F = F1/N,
                                         length(Arglist, Len),
                                         assertion(N == Len),
                                         Fapp =.. [F1|Arglist],
                                         (var(Range) -> Range = uninterpreted ; true), !,
                                         get_z3_declaration_map(M),
                                         z3_function_declaration(M, Fapp, Range).

typecheck_and_declare(Formulas, Assoc) :-
    assert_formula_list_types(Formulas), !, %% updates the global (backtrackable) type map
    type_inference_global:get_map(Assoc),
    assoc_to_list(Assoc, L),
    declare_type_list(L).


declare_type_list([]).
declare_type_list([A-B|R]) :- z3_declare(A, B), declare_type_list(R).
declare_type_list([A:B|R]) :- z3_declare(A, B), declare_type_list(R).


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
                foo(b) = c % this implies b = 0
               ]
               .

check_test_formulas(Formulas, R) :-
    test_formulas(Formulas),
    Conjunction =.. [and | Formulas],
    z3_push(Conjunction, R).

test(sat, [true(R == l_true)] ) :-
    check_test_formulas(_F, R).

test(typetest) :-
    test_formulas(Formulas),
    assert_formula_list_types(Formulas),
    type_inference_global:get_map(Map),
    assoc_to_list(Map, R),
    assertion(member(a-int, R)),
    assertion(member(f/1-lambda([foobarsort], int), R)).

test(nonsat, [true(R1 == l_true), true(R2 == l_false)] ) :-
    check_test_formulas(_Formulas, R1),
    z3_push(b=2, R2).


test(reals) :-
    z3_push(y:real > 2, R0),
    z3_push(a:real=div(x, y), R),
    z3_push(a = div(b:real, 4.0), R1),
    z3_push(a > 0.0, R2),
    assertion(R2 == l_true).

% interesting scenario: z3_push(a:real = div(x, y), R), z3_push(a = div(b:real, 4.0), R1), z3_model_map(M).
% reports on division-by-zero value.

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
%% z3:z3_push(b:int>c,R), z3:z3_push(and(a>d:int,b>e:int),R1), z3_push(f > b), z3_model_map(M), z3_is_consistent(f < a), z3_model_map(M1), z3_push(f > a), z3_model_map(M2).
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

:- end_tests(attribute_tests).

:- include(z3_unit_tests).
