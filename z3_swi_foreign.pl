%%% -*- Mode: Prolog; Module: z3; -*-

%% this is the lowest-level wrapper

:- module(z3_foreign, [
	      z3_reset_declarations/0,
	      z3_solver_check/2,
	      z3_solver_get_model/2,
	      z3_mk_solver/1,
	      z3_free_solver/1,
	      z3_assert/2,
	      z3_function_declaration/3
            ]).

:- load_foreign_library(z3_swi_foreign).

:- begin_tests(foreign_tests).


test(map_size) :-
    z3_declaration_map_size(X),
    integer(X).

test(reset) :-
    z3_reset_declarations,
    z3_declarations_string(S),
    assertion(S =@= "(ast-map)"),
    z3_declaration_map_size(X),
    assertion(X == 0).


is_pointer(X) :- integer(X).


test(context) :-
    z3_context(C),
    is_pointer(C).


test(solver) :-
    z3_mk_solver(S),
    is_pointer(S),
    z3_free_solver(S).


test(check_solver) :-
    z3_mk_solver(S),
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_solver_get_model(S, M),
    is_pointer(M),
    z3_free_solver(S).

test(symbols) :-
    z3_symbol(a, A1),
    z3_symbol(a, A2),
    assertion(A1 == A2),
    z3_symbol("asdf", S1),
    z3_symbol("asdf", S2),
    assertion(S1 == S2),
    assertion(\+ (A1 == S1)).

%% todo: wrap pointers in terms, for a little more typechecking:
%% solver(S), model(M), etc.

test(model_eval) :-
    z3_mk_solver(S),
    z3_function_declaration(a, int, _R1),
    z3_function_declaration(b, int, _R2),
    z3_assert(S, a=3),
    z3_assert(S, b=2),    
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_solver_get_model(S, Model),
    assertion(z3_model_eval(Model, a+a, 6)), % typo z3_model_eval(S,a,R) causes segfault!
    assertion(z3_model_eval(Model, a+b, 5)),
    assertion(z3_model_eval(Model, a*b, 6)),
    assertion(z3_model_eval(Model, a**b, 9)).


test(bad_types, [fail] ) :-
    z3_mk_solver(S),
    z3_function_declaration(a, real, _R1),
    z3_assert(S, a=3).

:- end_tests(foreign_tests).
