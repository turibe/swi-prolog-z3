%% -*- Mode: Prolog; Module: z3_swi_foreign; -*-


:- module(z3_swi_foreign, [
              
              % A handle bundles Z3 declarations, context, and solver.
              % Making and freeing handles:
              z3_new_handle/1,             %% -handle
              z3_free_handle/1,            %% +handle

              z3_assert/2,                 %% +handle, +formula  Asserts the formula, but does not do a solver check yet.
              z3_declarations/2,           %% +handle, -declarations
              z3_enum_declarations/2,      %% +handle, -declarations
              z3_free_model/2,             %% +handle, +model_pointer
              z3_declare_function/3,       %% +handle, +formula_schema, +type
              z3_remove_declaration/3,     %% +handle, +name, +arity
              z3_declare_enum/3,           %% +handle, +name, +list_of_values
              z3_model_eval/5,             %% +handle, +model_pointer, +formula, +completion_flag, -value
              z3_model_lists/2,            %% +handle, -map with lists for constants and functions
              z3_model_assocs/2,           %% +handle, -map with assocs for constants and functions
              z3_reset_declarations/1,     %% +handle  Resets all declarations, does not clear solvers.
              z3_solver_assertions/2,      %% +handle, -assertions
              z3_check/2,                  %% +handle, -status
              z3_check_and_print/2,        %% calls Z3_model_to_string
              z3_get_model/2,              %% +handle, -model_pointer
              z3_solver_pop/3,             %% +handle, +N, -new_scopes pop the solver N times
              z3_solver_push/2,            %% +handle, -new_scopes     push the solver one time
              z3_simplify/3,               %% +handle, +term, -term
              z3_solver_scopes/2,          %% +handle, -scopes

              %% for debugging:
              z3_declarations_string/2,    %% +handle, -string
              z3_enums_string/2,           %% +handle, -string

              %% estimates of Z3's memory use:
              z3_alloc_bytes/1,            %% -num_bytes
              z3_alloc/1,                  %% -string
              
              op(750, xfy, and), % =, >, etc. are 700 ; Local to the module
              op(751, xfy, or),
              op(740, xfy, <>)
            ]).


/** <module> Low-level Z3-SWI integration

This is the lowest-level Prolog wrapper.
It has no global variables except for those in the C code.

@author Tomas Uribe
@license MIT
*/

:- load_foreign_library(z3_swi_foreign).

:- set_prolog_flag(string_stack_tripwire, 20).

:- use_module(utils).

%% we now use "print_message" for error messages.

:- multifile prolog:(message/1).
prolog:message(z3_message(S)) --> {}, [S].
prolog:message(z3_message(F,L)) --> {swritef(S, F, L)}, [S].


%! z3_assert(+Handle, +Formula)
%  Adds formula to the handle's solver. Fails if needed declarations are missing.
%  Does not do a solver check.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_alloc_bytes(-Bytes)
%  Get approximate memory usage, in bytes, from Z3.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_check(+Handle, -Status)
%  Does a z3_check for Handle's solver, and returns Status.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_check_and_print(+Handle, -Status)
%  Does a z3_check for Handle's solver, printing a model if possible, and returns Status.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_declarations_string(+Handle, -String)
%  Gets a string representation of the declarations for Handle.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_declare_enum(+Handle, +EnumName, +ValueList)
%  Declares an enumeration type EnumName with values in ValueList.
%  Example: `z3_declare_enum(H, color, [black, white, red])`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_enums_string(+Handle, -String)
%  Gets a string describing the enum declarations for Handle.
%  (Defined in `z3_swi_foreign.c`).

%! z3_new_handle(+Handle)
%  Creates a new handle. Should be freed with z3_free_handle/1.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_free_handle(+Handle)
%  Low-level: frees Handle and all associated resources (context, solver, declarations).
%  (Defined in `z3_swi_foreign.c`.)

%! z3_free_model(+Handle, +ModelPointer)
%  Low-level: frees ModelPointer, a model for the given Handle/context.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_get_model(+Handle, -ModelPointer)
%  Low-level: gets a model for the given Handle/context. The model should be freed with z3_free_model/2.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_model_eval(+Handle, +ModelPointer, +Formula, +CompletionFlag, -Result)
%  Given a model for Handle, evaluates Formula, using the given CompletionFlag (`true/false`).
%  (Defined in `z3_swi_foreign.c`.)

%! z3_remove_declaration(+Handle, +Name, +Arity)
%  Removes the declaration for the given function or constant `Name/Arity`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_reset_declarations(+Handle)
%  Resets all declarations for Handle, except for the enum declarations.
%  (To reset the enum declarations, free Handle and make a new one.)
%  (Defined in `z3_swi_foreign.c`.)

%! z3_simplify(+Handle, +Formula, -FormulaOut)
%  Apply Z3's simplify to Formula.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_assertions(+Handle, -Assertions)
%  Get the assertions that have been added to Handle's solver.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_push(+Handle, -Scopes)
%  Does a z3_push for Handle's solver, and reports the new number of Scopes.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_pop(+Handle, +N, -Scopes)
%  Pops Handle's solver `N` times, and reports the new number of Scopes.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_scopes(+Handle, -Scopes)
%  Get the number of solver scopes for Handle's solver, in Scopes.
%  (Defined in `z3_swi_foreign.c`.)

%%%%%%%%%%%%%%%%%%%%%%%%%% End docs for predicates defined in the C interface.


%! z3_declare_function(+Handle, +Formula, +Type)
%  Declares term Formula to have sort Type, adding the declaration to Handle's map.
%  New declarations don't override old ones --- fails if there is a conflict.
%  Examples: z3_declare_function(H, a, int) ; z3_declare_function(H, f(int, int), real).
z3_declare_function(H, F, T) :- F == A/0, z3_declare_function(H, A, T).
z3_declare_function(H, F, T) :- z3_declare_function(H, F, T, _C).
% (Returned pointer is only useful for debugging, so we hide it here)

z3_model_lists(H, M, Map) :- z3_model_functions(H, M, F),
                             z3_model_constants(H, M, C),
                             sort(F, FS),
                             sort(C, CS),
                             Map = model{functions:FS, constants:CS}.


z3_model_assocs(H, M, Map) :- z3_model_functions(H, M, F),
                              z3_model_constants(H, M, C),
                              pair_list_to_assoc(F, Fmap),
                              pair_list_to_assoc(C, Cmap),
                              Map = model{functions:Fmap, constants:Cmap}.

%! z3_model_assocs(+Handle, -Model)
%  Gets a Prolog term representing a model for Handle's solver, using assoc maps.
z3_model_assocs(H, Model) :-
    must_be(ground, H),
    setup_call_cleanup(z3_get_model(H, M),
                       z3_model_assocs(H, M, Model),
                       z3_free_model(H, M)
                      ).


%! z3_model_lists(+Handle, -Model)
%  Gets a Prolog term representing a model for Handle's solver, using lists.
z3_model_lists(H, Model) :-
    setup_call_cleanup(z3_get_model(H, M),
                       z3_model_lists(H, M, Model),
                       z3_free_model(H, M)
                      ).


% Internal: constructs a (F/N:val) term from a (_some_binary(F,N):val) term
translate_entry(Entry, NewEntry) :-
    Entry = Key:Value,
    Key =.. [_, F, N],
    NK = F/N,
    NewEntry = (NK:Value).

%! z3_declarations(+Handle, -List)
%  Gets the function and constant declarations for Handle as a list.
z3_declarations(H, L) :- z3_get_declarations(H, LG), maplist(translate_entry, LG, L).

%! z3_enum_declarations(+Handle, -List)
%  Gets the enum declarations for Handle as a list.
z3_enum_declarations(H, L) :- z3_get_enum_declarations(H, LG), maplist(translate_entry, LG, L).


%! z3_alloc(-String)
%  Gets a human-readable description of the (approximate) number of bytes Z3 is currently allocating.
z3_alloc(S) :- z3_alloc_bytes(N), readable_bytes(N,S).

% When more than one thread is used, need to make sure that tests free Z3 structs when they're done
% (not just reset them).

:- Jobs = 1, set_test_options([jobs(Jobs), cleanup(true), output(on_failure)]).

:- begin_tests(z3_swi_foreign).

test(test_messages) :-
    print_message(informational, z3_message("testing informational message")),
    print_message(error, z3_message("testing error message %w", [1])),
    print_message(warning, z3_message("testing warning message")).


test(reset_declarations, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    % TODO: assert something
    z3_reset_declarations(H),
    z3_declarations_string(H, S),
    assertion(S =@= "(ast-map)").

is_pointer(X) :- integer(X).

test(check_solver, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_check(H, Status),
    assertion(Status == l_true),
    z3_get_model(H, M),
    is_pointer(M),
    z3_free_model(H, M).

test(symbol_pointers, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_symbol(H, a, A1),
    z3_symbol(H, a, A2),
    assertion(A1 == A2),
    z3_symbol(H, "asdf", S1),
    z3_symbol(H, "asdf", S2),
    assertion(S1 == S2),
    assertion(\+ (A1 == S1)).

%% todo: wrap pointers in terms, for a little more typechecking:
%% solver(S), model(M), etc.

test(model_eval,  [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))])  :-
    z3_declare_function(H, a, int),
    z3_declare_function(H, b, int),
    z3_assert(H, a=3),
    z3_assert(H, b=2),
    z3_check(H, Status),
    assertion(Status == l_true),
    setup_call_cleanup(
        z3_get_model(H, Model),
        (
            % TODO: use blobs or some other method to distinguish models and solvers.
            assertion(z3_model_eval(H, Model, a+a, false, 6)),
            assertion(z3_model_eval(H, Model, a+b, false, 5)),
            assertion(z3_model_eval(H, Model, a*b, false, 6)),
            assertion(z3_model_eval(H, Model, a**b, false, 9)),
            assertion(z3_model_eval(H, Model, z, false, z)), %% no completion
            assertion(z3_model_eval(H, Model, z, true, 0)), %% completion
            true
        ),
        z3_free_model(H, Model)
    ).


test(assert_test, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))]) :-
    z3_declare_function(S, a, bool),
    z3_declare_function(S, b, int),
    z3_declare_function(S, c, int),
    z3_assert(S, (a and (b > 0)) and (1.321 < c)),
    z3_check(S, Status),
    assertion(Status == l_true).

test(int_real_types, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    z3_declare_function(S, a, real),
    z3_assert(S, a=3).

test(get_model_no_check, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_declare_function(S, a, int),
    z3_assert(S, a = 3),
    %% get_model expected to fail:
    (z3_get_model(S, Model) -> z3_free_model(S, Model) ; fail).

test(incompatible_types1, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_declare_function(S, a, foo),
    z3_assert(S, a = 3),
    (z3_get_model(S, Model) -> z3_free_model(S, Model) ; fail).

test(incompatible_types2, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S)), fail]) :-
    z3_declare_function(S, a, foo),
    z3_declare_function(S, b, bar),
    z3_assert(S, a = b),
    (z3_get_model(S, Model) -> z3_free_model(S, Model) ; fail).


test(atleast_type, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    \+ z3_assert(H, atleast(a:bool, b:bool, c:bool)),
    z3_assert(H, atleast(a:bool, b:bool, c:bool, 2)).

test(atmost_type, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    \+ z3_assert(H, atmost(a:bool, b:bool, c:bool)),
    z3_assert(H, atmost(a:bool, b:bool, c:bool, 2)).

test(declare_fail1, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), fail] ) :-
    z3_declare_function(H, _X, int).

test(declare_fail2, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), fail] ) :-
    z3_declare_function(H, a, _Y).

test(declare_fail_different_types, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), fail] ) :-
    z3_declare_function(H, a, bool),
    z3_declare_function(H, a, int).

test(declare_fail_different_types1, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), fail] ) :-
    z3_declare_function(H, f(int), bool),
    z3_declare_function(H, f(bool), bool).

test(solver_push_pop, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_solver_push(H, X1), X1 == 1,
    z3_solver_push(H, X2), X2 == 2,
    z3_solver_scopes(H, 2),
    z3_solver_pop(H, 1, New_scopes),
    assertion(New_scopes == 1).

test(solver_pop, [ fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_solver_push(S, 1),
    z3_solver_pop(S, 10, _X).

:- set_prolog_flag(plunit_output, always).

test(fail_test, [ setup(Message = "a"),  cleanup(writeln(user_output,Message)), fail ]) :-
    %% Message = "cleanup message",
    writeln(user_output, "testing"),
    fail.

test(get_assertions, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    z3_assert(S, and(c:bool,x:bool)),
    z3_assert(S, a:int>3),
    z3_assert(S, b:int>1),
    z3_check(S, R),
    z3_solver_assertions(S, List),
    assertion(R == l_true),
    assertion(List =@= [b>1, a>3, c and x]).

test(real_assertion, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    z3_assert(S, x:real = 1.3).

test(roundtrips1, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, "i am a string", AS), z3_ast_to_term(H, AS, PS),
    assertion(PS == "i am a string"),
    term_to_z3_ast(H, 123, A1), z3_ast_to_term(H, A1, T1),
    assertion(T1 == 123),
    term_to_z3_ast(H, 1.4, A2), z3_ast_to_term(H, A2, T2),
    assertion(T2 == 7 / 5).

test(roundtrips2, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_declare_function(H, f(int,int,bool), int),
    z3_declare_function(H, g(bool), bool),
    z3_declare_function(H, c, bool),
    Term = f(a,b,g(c)), % a and b are int by default.
    term_to_z3_ast(H, Term, X),
    z3_ast_to_term(H, X, Y),
    assertion(Y == Term).

test(roundtrips_true_false, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, true, RT), z3_ast_to_term(H, RT, true),
    term_to_z3_ast(H, false, RF), z3_ast_to_term(H, RF, false).

%% This fails because "a" gets type int by default
test(default_int_fail, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ] ) :-
    z3_assert(S, a),
    z3_check(S, _R),
    setup_call_cleanup(
        z3_get_model(S, Model),
        z3_model_eval(S, Model, not(a), false, _V),
        z3_free_model(S, Model)
    ).

test(was_broken, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S)), true(V==false), true(R==l_true)]) :-
    z3_assert(S, a:bool),
    z3_check(S, R),
    setup_call_cleanup(
        z3_get_model(S, Model),
        z3_model_eval(S, Model, not(a), false, V),
        z3_free_model(S, Model)
    ).

test(should_fail, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_assert(S, a:bool),
    z3_assert(S, a:int > 1).

test(not_caught, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ] ) :-
    z3_assert(S, a:bool),
    z3_assert(S, a > -1),
    z3_check(S, l_true).

test(works, [true(V==false), true(R==l_true), setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_assert(S, a:bool),
    z3_check(S, R),
    setup_call_cleanup(
        z3_get_model(S, Model),
        z3_model_eval(S, Model, not(a:bool), false, V),
        z3_free_model(S, Model)
    ).

test(combined_bool_int, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_declare_function(S, f(int), int),
    z3_assert(S, f(a:int) > 1),
    z3_assert(S, f(b:bool) > 2),
    z3_check(S, l_true),
    z3_model_lists(S, Model),
    assertion(Model.constants == [a=4, b=false]).

test(arity_error, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_assert(S, =(a,b,c)).

test(neq_incompatible, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_assert(S, a:foo <> b:bar).

test(neq_numeric, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    z3_assert(S, a:bool <> b:real),
    z3_check(S, l_true).

% The C code does not handle <compound_term>:int annotations.
% The types for functions should be declared separately, if needed.
% The higher-level API, z3.pl, does handle this case.

test(nested_fail, [fail, setup(z3_new_handle(S)), cleanup(z3_free_handle(S))]) :-
    z3_assert(S, f(a:int):int = 3).

test(handle_ids) :-
    z3_new_handle(H1),
    z3_new_handle(H2),
    z3_handle_id(H1, I1),
    z3_handle_id(H2, I2),
    \+ I1 == I2,
    z3_free_handle(H1),
    z3_free_handle(H2).

test(simplify, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_simplify(H, a * 3 + a, T),
    assertion(T == 4 * a),
    z3_simplify(H, b + b + (b:int), T1),
    assertion(T1 == 3 * b).

:- end_tests(z3_swi_foreign).

:- begin_tests(z3_swi_foreign_bit_vectors).

test(create, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, a:bv(32) = int2bv(32, 12345)),
    z3_check(H, R),
    assertion(R == l_true),
    z3_model_lists(H, Model),
    assertion(Model.constants==[a=12345]).

test(bv2int, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, a:bv(32) = int2bv(32, -12345)),
    z3_assert(H, b:int = bv2int(a, true)), % signed
    z3_assert(H, c:int = bv2int(a, false)), % unsigned
    z3_check(H, l_true),
    z3_model_lists(H, Model),
    C = Model.constants,
    C == [a=4294954951, b= -12345, c=4294954951].

% add: z3_push(bvmul(a:bv(32),b:bv(32)) = int2bv(32, 1)), z3_model(M).

test(bvnumeral, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, a:bv(4) = bv_numeral([1,1,1,1])),
    z3_check(H, l_true),
    z3_model_lists(H, Model),
    C = Model.constants,
    assertion(C == [a=15]).

test(make_unsigned_int64, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    % z3_assert(S, a:int = mk_unsigned_int64(123,int)),
    z3_assert(S, a:bv(16) = mk_unsigned_int64(123, bv(16))),
    z3_check(S, l_true),
    z3_model_lists(S, Model),
    C = Model.constants,
    assertion(C == [a=123]).

test(make_numerals, [setup(z3_new_handle(S)), cleanup(z3_free_handle(S))] ) :-
    z3_assert(S, a:bv(16) = mk_numeral("123", bv(16))),
    z3_check(S, l_true),
    z3_model_lists(S, Model),
    C = Model.constants,
    assertion(C == [a=123]).

:- end_tests(z3_swi_foreign_bit_vectors).

:- begin_tests(basic_enums).

test(enums, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_declare_enum(H, color, [black, white, red]),
    z3_assert(H, and(a:color <> black, a:color <> white)),
    z3_check(H, l_true),
    z3_assert(H, a <> red),
    z3_check(H, l_false).

test(separate_enums, [setup((z3_new_handle(H1), z3_new_handle(H2))),
                      cleanup((z3_free_handle(H1), z3_free_handle(H2)))] ) :-
    z3_declare_enum(H1, color, [black, white]),
    z3_declare_enum(H1, food, [cereal, milk]),
    z3_declare_enum(H2, color, [green, blue]),
    % \+ z3_assert(H1, black = white),
    z3_assert(H2, black = white),
    z3_assert(H2, milk = 2),
    z3_assert(H1, and(x:color <> black,  x:color <> white)),
    z3_check(H1, l_false).
    

:- end_tests(basic_enums).

:- begin_tests(remove_declarations).

test(remove_decl, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, a:int > b:int),
    z3_remove_declaration(H,a,0),
    z3_assert(H, a:bool > b),
    z3_remove_declaration(H,b,0),
    z3_declare_function(H,f(int), int),
    z3_assert(H, f(a) > b),
    z3_remove_declaration(H,f,1),
    \+ z3_assert(H, f(a) > b).


:- end_tests(remove_declarations).


