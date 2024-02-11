%%% -*- Mode: Prolog; Module: z3; -*-

%% This is the lowest-level wrapper.
%% It has no global variables except those in the C code.

:- module(z3_swi_foreign, [
	      z3_assert/3,
	      z3_context/1,
	      z3_declarations_string/2,
	      z3_free_model/1,
	      z3_free_solver/1,
              z3_free_declaration_map/1,
	      z3_function_declaration/3,
	      z3_make_solver/1,
              z3_make_declaration_map/1,
              z3_declaration_map_size/2,
	      z3_model_eval/4,             %% +decl_map, +model_pointer, +formula, -value 
	      z3_model_map/2,
	      z3_reset_declaration_map/1,
	      z3_solver_assertions/2,
	      z3_solver_check/2,
	      z3_solver_check_and_print/2, % calls Z2_model_to_string
	      z3_solver_get_model/2,
	      z3_solver_pop/3,
	      z3_solver_push/2,
	      z3_solver_scopes/2,
	      op(750, xfy, and), % =, >, etc. are 700 ; Local to the module
              op(751, xfy, or),
              op(740, xfy, <>)
            ]).

:- load_foreign_library(z3_swi_foreign).

%% Next: solver and map should go together in a named map;
%% could even add the Z3 context to it later?

reset_declarations(M) :- ground(M), z3_reset_declaration_map(M).
reset_declarations(M) :- var(M), z3_make_declaration_map(M).

z3_print_declarations(M) :-
    z3_declarations_string(M, X), print_message(information, format(X, [])).


%% returned pointer is only useful for debugging, so we hide it here:
%% FIXME: change name, clarify semantics. New declarations don't override old ones?
z3_function_declaration(Map, A, B) :- z3_function_declaration(Map, A, B, _C).

z3_model_map(M, Map) :- z3_model_functions(M, F),
                        z3_model_constants(M, C),
                        Map = model{functions:F, constants:C}.

:- begin_tests(foreign_tests).


test(reset, [cleanup(z3_free_declaration_map(M))]) :-
    z3_make_declaration_map(M),
    z3_declarations_string(M, S),
    assertion(S =@= "(ast-map)"),
    z3_declaration_map_size(M, X),
    assertion(X == 0).


is_pointer(X) :- integer(X).


test(context) :-
    z3_context(context(C)),
    is_pointer(C).


test(solver) :-
    z3_make_solver(S),
    is_pointer(S),
    z3_free_solver(S).


test(check_solver) :-
    z3_make_solver(S),
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_solver_get_model(S, M),
    is_pointer(M),
    z3_free_solver(S).

test(symbol_pointers) :-
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
    z3_make_solver(S),
    reset_declarations(M),
    z3_function_declaration(M, a, int),
    z3_function_declaration(M, b, int),
    z3_assert(M, S, a=3),
    z3_assert(M, S, b=2),    
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_solver_get_model(S, Model),
    % typo z3_model_eval(S,a,R) causes segfault!
    % TODO: use blobs or some other method to distinguish models and solvers.
    assertion(z3_model_eval(M, Model, a+a, 6)),    
    assertion(z3_model_eval(M, Model, a+b, 5)),
    assertion(z3_model_eval(M, Model, a*b, 6)),
    assertion(z3_model_eval(M, Model, a**b, 9)),
    z3_free_model(Model),
    z3_free_declaration_map(M),
    z3_free_solver(S).


test(assert_test, [cleanup(z3_free_declaration_map(Map))]) :-
    z3_make_declaration_map(Map),
    z3_make_solver(S),
    z3_function_declaration(Map, a, bool),
    z3_function_declaration(Map, b, int),
    z3_function_declaration(Map, c, int),
    z3_assert(Map, S, (a and (b > 0)) and (1.321 < c)),
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_print_declarations(Map),
    z3_free_solver(S).

test(bad_types, [fail, cleanup((z3_free_solver(S), z3_free_declaration_map(M)))] ) :-
         z3_make_solver(S),
         z3_make_declaration_map(M),
         z3_function_declaration(M, a, real),
         z3_assert(M, S, a=3).

test(no_check, [fail]) :-
    setup_call_cleanup(
        (z3_make_solver(S),
         reset_declarations(Map)
        ),
        (z3_function_declaration(Map, a, int),
         z3_assert(Map, S, a = 3),
         z3_solver_get_model(S, _Model)
        ),
        z3_free_solver(S)
    ).

test(incompatible_types1, [fail]) :-
    z3_make_solver(S),
    reset_declarations(M),
    z3_function_declaration(M, a, foo),
    z3_assert(M, S, a = 3),
    z3_solver_get_model(S, _Model).

test(incompatible_types2, [fail]) :-
    z3_make_solver(S),
    reset_declarations(M),
    z3_function_declaration(M, a, foo),
    z3_function_declaration(M, b, bar),
    z3_assert(M, S, a = b),
    z3_solver_get_model(S, _Model).

test(at_least_fail, [fail]) :- %% TODO: add cleanup
    z3_make_declaration_map(M),
    z3_make_solver(S),
    z3_assert(M, S, atleast(a:bool, b:bool, c:bool)).


test(declare_fail1, [fail]) :-
    reset_declarations(M),
    z3_function_declaration(M, _X, int).

test(declare_fail2, [fail]) :-
    reset_declarations(M),
    z3_function_declaration(M, a, _Y).

test(declare_fail_diffent_types, [fail]) :-
    reset_declarations(M),
    z3_function_declaration(M, a, bool),
    z3_function_declaration(M, a, int).

test(declare_fail_diffent_types1, [fail, cleanup(z3_free_declaration_map(M)) ]) :-
    reset_declarations(M),
    z3_function_declaration(M, f(int), bool),
    z3_function_declaration(M, f(bool), bool).

test(solver_push_pop, [cleanup(z3_free_solver(S))] ) :-
    z3_make_solver(S),
    z3_solver_push(S, 1),
    z3_solver_push(S, 2),
    z3_solver_scopes(S, 2),
    z3_solver_pop(S, 1, New_scopes),
    assertion(New_scopes == 1).

test(solver_pop, [fail]) :-
    z3_make_solver(S),
    z3_solver_push(S, 1),
    z3_solver_pop(S, 10, _X).


test(get_assertions) :-
    reset_declarations(M),
    z3_make_solver(S), z3_assert(M, S, and(c:bool,x:bool)), z3_assert(M, S, a:int>3), z3_assert(M, S, b:int>1),
    z3_solver_check(S,R),  z3_solver_assertions(S, List),
    assertion(R == l_true),
    assertion(List =@= [b>1, a>3, c and x]).

test(real_assertion) :-
    reset_declarations(M),
    z3_make_solver(S),
    z3_assert(M, S, x:real = 1.3).

test(roundtrips1) :-
    reset_declarations(M),
    term_to_z3_ast(M, "i am a string", AS), z3_ast_to_term(AS, PS),
    assertion(PS == "i am a string"),
    term_to_z3_ast(M, 123, A1), z3_ast_to_term(A1, T1),
    assertion(T1 == 123),
    term_to_z3_ast(M, 1.4, A2), z3_ast_to_term(A2, T2),
    assertion(T2 == 7 div 5).


test(roundtrips2) :-
    reset_declarations(M),
    z3_function_declaration(M, f(int,int,bool),int),
    z3_function_declaration(M, g(bool),bool),
    z3_function_declaration(M, c,bool),
    Term = f(a,b,g(c)), % a and b are int by default.
    term_to_z3_ast(M, Term, X),
    z3_ast_to_term(X,Y),
    assertion(Y == Term).

%% TODO: this does not work because "a" gets type int by default
test(default_int_fail, [fail, cleanup((z3_free_model(Model), z3_free_declaration_map(Map))) ]) :-
    reset_declarations(Map),
    z3_make_solver(S),
    z3_assert(Map, S, a),
    z3_solver_check(S, _R),
    z3_solver_get_model(S, Model),
    z3_model_eval(Map, Model, not(a), _V).

test(was_broken, [true(V==false), true(R==l_true)]) :-
    reset_declarations(Map),
    z3_make_solver(S),
    z3_assert(Map, S, a:bool),
    z3_solver_check(S, R),
    z3_solver_get_model(S, Model),
    z3_model_eval(Map, Model, not(a), V),
    z3_free_model(Model),
    z3_free_solver(S),
    z3_free_declaration_map(Map).

test(should_fail, [fail]) :-
    reset_declarations(Map),
    setup_call_cleanup(
        z3_make_solver(S),
        (z3_assert(Map, S, a:bool),
         z3_assert(Map, S, a:int > 1)
        ),
        (z3_free_solver(S), z3_free_declaration_map(Map))
    ).

%% TODO: fix this one?
test(not_caught, [cleanup((z3_free_solver(S), z3_free_declaration_map(M)))] ) :-
    reset_declarations(M),
    z3_make_solver(S),
    z3_assert(M, S, a:bool),
    z3_assert(M, S, a > -1),
    z3_solver_check(S, l_true).

test(works, [true(V==false), true(R==l_true)]) :-
    reset_declarations(Map),
    z3_make_solver(S),
    z3_assert(Map, S, a:bool),
    z3_solver_check(S, R),
    setup_call_cleanup(
        z3_solver_get_model(S, Model),
        z3_model_eval(Map, Model, not(a:bool), V),
        (z3_free_model(Model), z3_free_declaration_map(Map))
    ).


%% FIXME:
%% does not fail: z3_make_solver(S), z3_make_declaration_map(M), z3_function_declaration(M, f(int), int), z3_assert(M, S, f(a:int) > 1), z3_assert(M, S, f(b:bool) > 2).

:- end_tests(foreign_tests).
