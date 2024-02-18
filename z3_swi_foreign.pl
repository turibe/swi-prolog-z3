%%% -*- Mode: Prolog; Module: z3_swi_foreign; -*-

/** <module> Low-level Z3-SWI integration

This is the lowest-level Prolog wrapper.
It has no global variables except those in the C code.

@author Tomas Uribe
@license MIT
*/

:- module(z3_swi_foreign, [
              z3_assert/2,
              z3_context/1,
              z3_declarations_string/1,
              z3_free_model/1,
              z3_free_solver/1,
              z3_declare_function/2,
              z3_make_solver/1,
              z3_mk_enumeration_sort/2,
              z3_model_eval/4,             %% +model_pointer, +formula, +completion_flag, -value
              z3_model_map_for_solver/2,
              z3_reset_declarations/0,
              z3_solver_assertions/2,
              z3_solver_check/2,
              z3_solver_check_and_print/2, % calls Z2_model_to_string
              z3_solver_get_model/2,
              z3_solver_pop/3,
              z3_solver_push/2,
              z3_simplify_term/2,
              z3_solver_scopes/2,
              z3_reset_context/0, % invalidates solvers, declaration maps
              z3_get_enum_declarations/1,
              z3_get_declarations/1,
              op(750, xfy, and), % =, >, etc. are 700 ; Local to the module
              op(751, xfy, or),
              op(740, xfy, <>)
            ]).

:- load_foreign_library(z3_swi_foreign).


%% Declares term F to have sort T, adding the declaration to the map.
%% New declarations don't override old ones --- fails if there is a conflict.
%% (Returned pointer is only useful for debugging, so we hide it here)
%% examples: z3_declare_function(a, int) ; z3_declare_function(f(int, int), real).

z3_declare_function(F, T) :- z3_declare_function(F, T, _C).

z3_model_map(M, Map) :- z3_model_functions(M, F),
                        z3_model_constants(M, C),
                        sort(F, FS),
                        sort(C, CS),
                        Map = model{functions:FS, constants:CS}.


% gets a Prolog term representing a model for the given solver S:
z3_model_map_for_solver(S, Model) :-
    setup_call_cleanup(z3_solver_get_model(S,M),
                       z3_model_map(M, Model),
                       z3_free_model(M)
                      ).


:- begin_tests(foreign_tests).


test(reset_declarations) :-
    z3_reset_declarations,
    z3_declarations_string(S),
    assertion(S =@= "(ast-map)").

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
    z3_declare_function(a, int),
    z3_declare_function(b, int),
    z3_assert(S, a=3),
    z3_assert(S, b=2),    
    z3_solver_check(S, Status),
    assertion(Status == l_true),
    z3_solver_get_model(S, Model),
    % TODO: use blobs or some other method to distinguish models and solvers.
    assertion(z3_model_eval(Model, a+a, false, 6)),
    assertion(z3_model_eval(Model, a+b, false, 5)),
    assertion(z3_model_eval(Model, a*b, false, 6)),
    assertion(z3_model_eval(Model, a**b, false, 9)),
    assertion(z3_model_eval(Model, z, false, z)), %% no completion
    assertion(z3_model_eval(Model, z, true, 0)), %% completion
    z3_free_model(Model),
    z3_free_solver(S).


test(assert_test, [cleanup(z3_free_solver(S))]) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_declare_function(a, bool),
    z3_declare_function(b, int),
    z3_declare_function( c, int),
    z3_assert(S, (a and (b > 0)) and (1.321 < c)),
    z3_solver_check(S, Status),
    assertion(Status == l_true).

test(int_real_types, [cleanup(z3_free_solver(S))] ) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_declare_function(a, real),
    z3_assert(S, a=3).

test(no_check, [fail]) :-
    setup_call_cleanup(
        (z3_make_solver(S),
         z3_reset_declarations
        ),
        (z3_declare_function(a, int),
         z3_assert(S, a = 3),
         z3_solver_get_model(S, _Model)
        ),
        z3_free_solver(S)
    ).

test(incompatible_types1, [fail]) :-
    z3_make_solver(S),
    z3_reset_declarations,
    z3_declare_function(a, foo),
    z3_assert(S, a = 3),
    z3_solver_get_model(S, _Model).

test(incompatible_types2, [fail]) :-
    z3_make_solver(S),
    z3_reset_declarations,
    z3_declare_function(a, foo),
    z3_declare_function(b, bar),
    z3_assert(S, a = b),
    z3_solver_get_model(S, _Model).

test(at_least_fail, [fail, cleanup(z3_free_solver(S))]) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, atleast(a:bool, b:bool, c:bool)).

test(declare_fail1, [fail]) :-
    z3_reset_declarations,
    z3_declare_function(_X, int).

test(declare_fail2, [fail]) :-
    z3_reset_declarations,
    z3_declare_function(a, _Y).

test(declare_fail_different_types, [fail]) :-
    z3_reset_declarations,
    z3_declare_function(a, bool),
    z3_declare_function(a, int).

test(declare_fail_different_types1, [fail]) :-
    z3_reset_declarations,
    z3_declare_function(f(int), bool),
    z3_declare_function(f(bool), bool).

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
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, and(c:bool,x:bool)),
    z3_assert(S, a:int>3),
    z3_assert(S, b:int>1),
    z3_solver_check(S,R),
    z3_solver_assertions(S, List),
    assertion(R == l_true),
    assertion(List =@= [b>1, a>3, c and x]).

test(real_assertion) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, x:real = 1.3).

test(roundtrips1) :-
    z3_reset_declarations,
    term_to_z3_ast("i am a string", AS), z3_ast_to_term(AS, PS),
    assertion(PS == "i am a string"),
    term_to_z3_ast(123, A1), z3_ast_to_term(A1, T1),
    assertion(T1 == 123),
    term_to_z3_ast(1.4, A2), z3_ast_to_term(A2, T2),
    assertion(T2 == 7 / 5).

test(roundtrips2) :-
    z3_reset_declarations,
    z3_declare_function(f(int,int,bool),int),
    z3_declare_function(g(bool),bool),
    z3_declare_function(c,bool),
    Term = f(a,b,g(c)), % a and b are int by default.
    term_to_z3_ast(Term, X),
    z3_ast_to_term(X,Y),
    assertion(Y == Term).

test(roundtrips_true_false) :-
    z3_reset_declarations,
    term_to_z3_ast(true, RT), z3_ast_to_term(RT, true),
    term_to_z3_ast(false, RF), z3_ast_to_term(RF, false).

%% This fails because "a" gets type int by default
test(default_int_fail, [fail, cleanup(z3_free_model(Model)) ]) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, a),
    z3_solver_check(S, _R),
    z3_solver_get_model(S, Model),
    z3_model_eval(Model, not(a), false, _V).

test(was_broken, [true(V==false), true(R==l_true)]) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, a:bool),
    z3_solver_check(S, R),
    z3_solver_get_model(S, Model),
    z3_model_eval(Model, not(a), false, V),
    z3_free_model(Model),
    z3_free_solver(S).

test(should_fail, [fail]) :-
    z3_reset_declarations,
    setup_call_cleanup(
        z3_make_solver(S),
        (z3_assert(S, a:bool),
         z3_assert(S, a:int > 1)
        ),
        (z3_free_solver(S), true)
    ).

%% TODO: fix this one?
test(not_caught, [cleanup((z3_free_solver(S), true))] ) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_assert(S, a:bool),
    z3_assert(S, a > -1),
    z3_solver_check(S, l_true).

test(works, [true(V==false), true(R==l_true)]) :-
    z3_make_solver(S),
    z3_assert(S, a:bool),
    z3_solver_check(S, R),
    setup_call_cleanup(
        z3_solver_get_model(S, Model),
        z3_model_eval(Model, not(a:bool), false, V),
        (z3_free_model(Model), true)
    ).


test(combined_bool_int, [cleanup(free_solver(S)) ]) :-
    z3_reset_declarations,
    z3_make_solver(S),
    z3_declare_function(f(int), int),
    z3_assert(S, f(a:int) > 1),
    z3_assert(S, f(b:bool) > 2),
    z3_solver_check(S, l_true),
    z3_model_map_for_solver(S,Model),
    assertion(Model.constants == [a-4, b-false]).

test(arity_error, [fail]) :-
    z3_make_solver(S),
    z3_reset_declarations,
    z3_assert(S, =(a,b,c)).

test(neq_incompatible, [fail]) :-
    z3_make_solver(S),
    z3_assert(S, a:foo <> b:bar).

test(neq_numeric) :-
    z3_make_solver(S),
    z3_reset_declarations,
    z3_assert(S, a:bool <> b:real),
    z3_solver_check(S, l_true).

% The C code does not handle <compound_term>:int annotations.
% The types for functions should be declared separately, if needed.
% The higher-level API, z3.pl, does handle this case.

test(nested_fail, [fail]) :-
    z3_make_solver(S),
    z3_reset_declarations,
    z3_assert(S, f(a:int):int = 3).

test(enums, cleanup(z3_reset_context)) :-
    z3_reset_context,
    z3_make_solver(S),
    z3_mk_enumeration_sort(color, [black, white, red]),
    z3_assert(S, and(a:color <> black, a:color <> white)),
    z3_solver_check(S, l_true),
    z3_assert(S, a <> red),
    z3_solver_check(S, l_false).

:- end_tests(foreign_tests).
