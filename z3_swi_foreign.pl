%% -*- Mode: Prolog; Module: z3_swi_foreign; -*-


:- module(z3_swi_foreign, [
              
              % A handle bundles Z3 declarations, context, and solver.
              % Making and freeing handles:
              z3_new_handle/1,             %% -handle
              z3_free_handle/1,            %% +handle

              z3_assert/2,                 %% +handle, +formula  Asserts the formula, but does not do a solver check yet.
              z3_declarations/2,           %% +handle, -declarations
              z3_enum_declarations/2,      %% +handle, -declarations
              z3_free_model/2,             %% +handle, +model
              z3_declare_function/3,       %% +handle, +formula_schema, +type
              z3_remove_declaration/3,     %% +handle, +name, +arity
              z3_declare_enum/3,           %% +handle, +name, +list_of_values
              z3_model_eval/5,             %% +handle, +model, +formula, +completion_flag, -value
              z3_model_lists/2,            %% +handle, -map with lists for constants and functions
              z3_model_assocs/2,           %% +handle, -map with assocs for constants and functions
              z3_reset_declarations/1,     %% +handle  Resets all declarations, does not clear solvers.
              z3_solver_assertions/2,      %% +handle, -assertions
              z3_check/2,                  %% +handle, -status
              z3_check_and_print/2,        %% calls Z3_model_to_string
              z3_get_model/2,              %% +handle, -model
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

Errors: argument errors raise ISO error terms. These include unbound arguments (an unbound variable
anywhere in a formula raises `instantiation_error`), wrongly typed arguments, out-of-range numbers,
and invalid handles or models (`type_error(z3_handle, _)`, `existence_error(z3_handle, _)`, and so on).
A formula that is a valid Prolog term but not a valid Z3 formula, such as a sort mismatch, an undeclared
function, or a built-in with the wrong arity, makes the predicate fail, printing a message.

Handles may be shared between threads; calls on the same handle are serialized.

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

%! z3_new_handle(-Handle) is det.
%  Creates a new handle, a `z3_handle` blob that prints as `<z3_handle>(Id)`.
%  Its Z3 context is freed by z3_free_handle/1, or when the blob is garbage collected.
%  Freeing explicitly is recommended, since contexts are large and atom garbage collection may not run soon.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_free_handle(+Handle) is det.
%  Low-level: frees the resources of Handle (context, solver, declarations) and of its models.
%  Using Handle afterwards, including freeing it again, raises `existence_error(z3_handle, Handle)`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_free_model(+Handle, +Model) is det.
%  Low-level: frees Model, a model for the given Handle/context.
%  Using Model afterwards raises `existence_error(z3_model, Model)`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_get_model(+Handle, -Model) is semidet.
%  Low-level: gets a model for the given Handle/context, as a `z3_model` blob. Fails if there is no model.
%  The model can be freed with z3_free_model/2; otherwise it is freed when garbage collected.
%  Using a model with a handle other than its own raises `permission_error(access, z3_model, Model)`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_model_eval(+Handle, +Model, +Formula, +CompletionFlag, -Result)
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
% (The returned declaration, a z3_ast blob, is only useful for debugging, so we hide it here.)

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

is_model(X) :- blob(X, z3_model).

test(check_solver, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_check(H, Status),
    assertion(Status == l_true),
    z3_get_model(H, M),
    is_model(M),
    z3_free_model(H, M).

test(symbol_pointers, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_symbol(H, a, A1),
    z3_symbol(H, a, A2),
    assertion(A1 == A2),
    z3_symbol(H, "asdf", S1),
    z3_symbol(H, "asdf", S2),
    assertion(S1 == S2),
    assertion(\+ (A1 == S1)).


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

test(declare_fail1, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), throws(error(instantiation_error, _))] ) :-
    z3_declare_function(H, _X, int).

test(declare_fail2, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), throws(error(instantiation_error, _))] ) :-
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

% Regression tests for bugs fixed in the C wrapper.

:- begin_tests(c_wrapper_fixes).

% bvnand used to build bvand.
test(bvnand, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, bvnand(a:bv(4), b:bv(4)), A),
    z3_ast_string(H, A, S),
    assertion(sub_string(S, _, _, _, "bvnand")),
    % bits are least-significant first: 3 nand 5 = ~1 = 14 in 4 bits.
    z3_assert(H, c:bv(4) = bvnand(bv_numeral([1,1,0,0]), bv_numeral([1,0,1,0]))),
    z3_check(H, l_true),
    z3_model_lists(H, Model),
    assertion(Model.constants == [c=14]).

% A negative pop count used to abort the process via a C assert.
test(pop_negative, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                    throws(error(domain_error(not_less_than_zero, -1), _))] ) :-
    z3_solver_push(H, _),
    z3_solver_pop(H, -1, _).

% z3_solver_push/2 used to reject a bound output, so z3_solver_push(H, 1) always failed.
test(push_bound_output, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_solver_push(H, 1),
    \+ z3_solver_push(H, 5),    % wrong count fails...
    z3_solver_scopes(H, N),
    assertion(N == 1),          % ...without pushing
    z3_solver_push(H, 2).

test(pop_not_integer,[setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                       throws(error(type_error(integer, foo), _))] ) :-
    z3_solver_pop(H, foo, _).

test(pop_after_error, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_solver_push(H, _),
    catch(z3_solver_pop(H, -1, _), error(domain_error(_, _), _), true),
    z3_solver_pop(H, 1, N),
    assertion(N == 0).

% on, off and fail used to become Boolean constants.
test(on_off_fail_are_constants, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                                 forall(member(Atom, [on, off, fail]))] ) :-
    term_to_z3_ast(H, Atom, A),
    z3_ast_to_term(H, A, T),
    assertion(T == Atom).

test(on_is_an_int_constant, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, on > 5),
    z3_check(H, l_true).

% mk_unsigned_int64 used to truncate to 32 bits and ignore bad values.
test(unsigned_int64_large, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, mk_unsigned_int64(5000000000, int), A),
    z3_ast_to_term(H, A, T),
    assertion(T == 5000000000).

test(unsigned_int64_bv64, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    Max is 2^64 - 1,
    z3_assert(H, a:bv(64) = mk_unsigned_int64(Max, bv(64))),
    z3_check(H, l_true),
    z3_model_lists(H, Model),
    assertion(Model.constants == [a=Max]).

test(unsigned_int64_negative, [fail, setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, mk_unsigned_int64(-1, int), _).

test(unsigned_int64_bad_sort, [fail, setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, mk_unsigned_int64(1, f(x)), _).

% Unconvertible subterms used to be passed to Z3 as NULL (bv2int crashed).
test(null_subterms, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                     forall(member(Term, [bv2int(undeclared(x), true),
                                          int2bv(8, undeclared(x)),
                                          bvadd_no_overflow(undeclared(x), b:bv(8), true),
                                          bvmul_no_overflow(b:bv(8), undeclared(x), false),
                                          bvsub_no_underflow(undeclared(x), undeclared(x), true)]))] ) :-
    \+ term_to_z3_ast(H, Term, _).

test(prolog_rational, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_simplify(H, 1r3, T),
    assertion(T == 1/3).

% Paths through compound_to_ast that used to leak the subterms array.
% (These check the results; the leak itself is not observable from Prolog.)
test(compound_early_returns, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, between(x:int, 1, 3)),
    z3_assert(H, x:int <> y:real),
    z3_check(H, l_true),
    \+ term_to_z3_ast(H, between(x, 1), _),       % arity error
    \+ term_to_z3_ast(H, undeclared(x), _),        % missing declaration
    z3_assert(H, x > 2),
    z3_check(H, l_true),
    z3_model_lists(H, Model),
    assertion(memberchk(x=3, Model.constants)).

% Removing a missing declaration used to trigger a Z3 error.
test(remove_missing_declaration, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    \+ z3_remove_declaration(H, nosuch, 0),
    z3_assert(H, a:int > 1),
    z3_check(H, l_true).

% z3_declare_enum argument checking.
test(enum_name_not_atom, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                          throws(error(type_error(atom, 3), _))] ) :-
    z3_declare_enum(H, 3, [a]).

test(enum_name_unbound, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                         throws(error(instantiation_error, _))] ) :-
    z3_declare_enum(H, _, [a]).

test(enum_improper_list, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                          throws(error(type_error(list, [a|b]), _))] ) :-
    z3_declare_enum(H, c, [a|b]).

test(enum_partial_list, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                         throws(error(instantiation_error, _))] ) :-
    z3_declare_enum(H, c, [a|_]).

test(enum_non_ground, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                       throws(error(instantiation_error, _))] ) :-
    z3_declare_enum(H, c, [a, _]).

test(enum_empty, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                  throws(error(domain_error(non_empty_list, []), _))] ) :-
    z3_declare_enum(H, c, []).

test(enum_compound_value, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                           throws(error(type_error(atom, f(x)), _))] ) :-
    z3_declare_enum(H, c, [f(x)]).

test(enum_redeclare_fails, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_declare_enum(H, c, [red, green]),
    \+ z3_declare_enum(H, c, [red, green]),
    z3_assert(H, x:c <> red),
    z3_check(H, l_true).

% bv_numeral used to keep going on a non-boolean element, using uninitialized bits.
test(bv_numeral_bad_lists, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                            forall(member(L, [[1, foo], [1|x], []]))] ) :-
    \+ term_to_z3_ast(H, bv_numeral(L), _).

test(bv_numeral_partial_list, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                               throws(error(instantiation_error, _))] ) :-
    term_to_z3_ast(H, bv_numeral([1|_]), _).

% Non-positive bit-vector widths used to reach Z3 as huge unsigned values.
test(bad_bv_widths, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                     forall(member(T, [int2bv(0, 5), int2bv(-1, 5), a:bv(0) = a, b:bv(-3) = b]))] ) :-
    \+ term_to_z3_ast(H, T, _).

% The = check now only lets Int and Real mix.
test(eq_sort_mismatches, [setup((z3_new_handle(H), z3_declare_enum(H, color, [red, blue]))),
                          cleanup(z3_free_handle(H)),
                          forall(member(T, [a:bool = b:int, c:int = d:color, e:bool = f:color]))] ) :-
    \+ term_to_z3_ast(H, T, _).

test(eq_int_real_mix, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, x:int = y:real),
    z3_assert(H, y = 2.0),
    z3_check(H, l_true).

% <> still treats Bool as numeric, as Z3 does in arithmetic.
test(neq_bool_real, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, c:bool <> d:real),
    z3_check(H, l_true).

% Integer symbols used to be truncated from long to int.
test(int_symbol_range, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_symbol(H, 5, S1),
    z3_symbol(H, 5, S2),
    assertion(S1 == S2),
    Big is 2^40,
    \+ z3_symbol(H, Big, _).

% z3_check/2 used PL_get_pointer instead of PL_get_pointer_ex.
test(check_bad_handle, [throws(error(type_error(_, foo), _))] ) :-
    z3_check(foo, _).

:- end_tests(c_wrapper_fixes).



% Handles and models are blobs, so stale or made-up ones raise errors instead of crashing.

:- begin_tests(handle_blobs).

test(handle_is_blob, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    assertion(blob(H, z3_handle)),
    z3_handle_id(H, Id),
    format(string(S), "~p", [H]),
    format(string(Expected), "<z3_handle>(~w)", [Id]),
    assertion(S == Expected).

test(not_a_handle, [throws(error(type_error(z3_handle, 12345), _))] ) :-
    z3_check(12345, _).

test(unbound_handle, [throws(error(instantiation_error, _))] ) :-
    z3_check(_, _).

test(use_after_free, [setup(z3_new_handle(H)), throws(error(existence_error(z3_handle, H), _))] ) :-
    z3_free_handle(H),
    z3_check(H, _).

test(double_free, [setup(z3_new_handle(H)), throws(error(existence_error(z3_handle, H), _))] ) :-
    z3_free_handle(H),
    z3_free_handle(H).

test(model_is_blob, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_check(H, l_true),
    z3_get_model(H, M),
    assertion(blob(M, z3_model)),
    z3_free_model(H, M).

test(model_use_after_free, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_check(H, l_true),
    z3_get_model(H, M),
    z3_free_model(H, M),
    catch(z3_model_eval(H, M, 1, false, _), E, true),
    assertion(E = error(existence_error(z3_model, M), _)),
    catch(z3_free_model(H, M), E2, true),
    assertion(E2 = error(existence_error(z3_model, M), _)).

test(model_wrong_handle, [setup((z3_new_handle(H1), z3_new_handle(H2))),
                          cleanup((z3_free_handle(H1), z3_free_handle(H2)))] ) :-
    z3_check(H1, l_true),
    z3_get_model(H1, M),
    catch(z3_model_constants(H2, M, _), E, true),
    assertion(E = error(permission_error(access, z3_model, M), _)),
    z3_free_model(H1, M).

test(handle_as_model, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                       throws(error(type_error(z3_model, H), _))] ) :-
    z3_free_model(H, H).

% Freeing a handle invalidates its models; collecting them afterwards must not touch the dead context.
test(model_outlives_handle) :-
    z3_new_handle(H),
    z3_check(H, l_true),
    z3_get_model(H, M),
    z3_free_handle(H),
    catch(z3_model_constants(H, M, _), E, true),
    assertion(E = error(existence_error(z3_handle, H), _)),
    garbage_collect_atoms.

unfreed_handle :- z3_new_handle(H), z3_assert(H, a:int > 3), z3_check(H, _).

% Handles that are never freed are reclaimed by atom garbage collection.
test(gc_reclaims_handles) :-
    garbage_collect_atoms,
    forall(between(1, 20, _), unfreed_handle),
    z3_alloc_bytes(Live),
    garbage_collect_atoms,
    z3_alloc_bytes(After),
    assertion(After < Live).

unfreed_model(H) :- z3_get_model(H, _).

% Models that are never freed are queued when collected and released on the handle's next use.
test(gc_reclaims_models, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, x:int > 3),
    z3_check(H, l_true),
    forall(between(1, 500, _), unfreed_model(H)),
    garbage_collect_atoms,
    z3_check(H, l_true),
    z3_get_model(H, M),
    z3_model_lists(H, Model),
    assertion(Model.constants = [x=_]),
    z3_free_model(H, M).

:- end_tests(handle_blobs).

% A handle shared between threads: calls on it are serialized by a per-handle lock.

:- begin_tests(handle_threads).

shared_handle_work(H, I) :-
    forall(between(1, 100, J),
           ( format(atom(X), "x~w_~w", [I, J]),
             z3_solver_push(H, _),
             z3_assert(H, X:int > J),
             z3_check(H, l_true),
             ( z3_get_model(H, M) -> z3_free_model(H, M) ; true ),
             z3_simplify(H, X + X, _),
             z3_solver_pop(H, 1, _) )).

% Without the lock this crashed the process.
test(shared_handle, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    findall(T, (between(1, 4, I), thread_create(shared_handle_work(H, I), T)), Ts),
    maplist(thread_join, Ts, Statuses),
    assertion(Statuses == [true, true, true, true]),
    z3_solver_scopes(H, N),
    assertion(N == 0).

test(handle_per_thread) :-
    findall(T, (between(1, 4, _),
                thread_create(setup_call_cleanup(z3_new_handle(H),
                                                 (z3_assert(H, a:int > 1), z3_check(H, l_true)),
                                                 z3_free_handle(H)), T)),
            Ts),
    maplist(thread_join, Ts, Statuses),
    assertion(Statuses == [true, true, true, true]).

test(freed_in_other_thread, [setup(z3_new_handle(H)), throws(error(existence_error(z3_handle, H), _))] ) :-
    thread_create(z3_free_handle(H), T),
    thread_join(T, true),
    z3_check(H, _).

:- end_tests(handle_threads).

% Argument errors raise ISO errors; formulas that are valid Prolog but not valid Z3 still fail.

:- begin_tests(argument_errors).

test(new_handle_bound, [throws(error(uninstantiation_error(foo), _))] ) :-
    z3_new_handle(foo).

unbound_formula(H, z3_assert(H, _)).
unbound_formula(H, z3_assert(H, a:int > _)).
unbound_formula(H, z3_assert(H, a:_ > 1)).
unbound_formula(H, z3_assert(H, bv2int(a:bv(8), _) > 1)).
unbound_formula(H, z3_assert(H, int2bv(_, 5) = a:bv(8))).
unbound_formula(H, z3_simplify(H, _ + 1, _)).
unbound_formula(H, term_to_z3_ast(H, f(_), _)).

test(unbound_in_formula, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                          forall(unbound_formula(H, Goal))] ) :-
    catch(Goal, E, true),
    assertion(nonvar(E)),
    assertion(E = error(instantiation_error, _)).

test(unbound_in_model_eval, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_check(H, l_true),
    z3_get_model(H, M),
    catch(z3_model_eval(H, M, _ + 1, false, _), E, true),
    z3_free_model(H, M),
    assertion(E = error(instantiation_error, _)).

bad_declaration(z3_declare_function(_, f(_), int),   instantiation_error).
bad_declaration(z3_declare_function(_, a, f(_)),     instantiation_error).
bad_declaration(z3_declare_function(_, 3, int),      type_error(callable, 3)).
bad_declaration(z3_declare_function(_, "a", int),    type_error(callable, "a")).
bad_declaration(z3_declare_function(_, a, 3),        type_error(callable, 3)).

test(declare_function_errors, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                               forall(bad_declaration(Goal0, Expected))] ) :-
    Goal0 =.. [Name, _ | Args],
    Goal =.. [Name, H | Args],
    catch(Goal, error(E, _), true),
    assertion(E =@= Expected).

bad_removal(_, 0,  instantiation_error).
bad_removal(3, 0,  type_error(atom, 3)).
bad_removal(a, _,  instantiation_error).
bad_removal(a, x,  type_error(integer, x)).
bad_removal(a, -1, domain_error(not_less_than_zero, -1)).

test(remove_declaration_errors, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                                 forall(bad_removal(Name, Arity, Expected))] ) :-
    catch(z3_remove_declaration(H, Name, Arity), error(E, _), true),
    assertion(E =@= Expected).

% These are malformed formulas, not argument errors: they still fail.
malformed(a:foo = b:bar).
malformed(=(a, b, c)).
malformed(undeclared(a) > 1).
malformed(f(a:int):int = 3).
malformed(int2bv(0, 5) = a:bv(8)).
malformed(mk_unsigned_int64(-1, int) = 1).

test(malformed_formulas_fail, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                               forall(malformed(F))] ) :-
    \+ z3_assert(H, F).

:- end_tests(argument_errors).

% ASTs, declarations and symbols handed to Prolog are blobs tied to their handle,
% so a made-up or stale one raises an error instead of crashing.

:- begin_tests(object_blobs).

test(ast_is_blob, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    term_to_z3_ast(H, 1 + 2, A),
    assertion(blob(A, z3_ast)),
    term_to_z3_ast(H, 1 + 2, A2),
    assertion(A == A2),                 % the same AST gives the same blob
    z3_ast_string(H, A, S),
    assertion(S == "(+ 1 2)").

test(symbol_is_blob, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_symbol(H, a, S),
    assertion(blob(S, z3_symbol)).

test(declaration_is_ast, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_declare_function(H, f(int), bool, D),
    assertion(blob(D, z3_ast)),
    z3_ast_string(H, D, S),
    assertion(S == "(declare-fun f (Int) Bool)").

% These used to dereference an arbitrary integer as a pointer.
test(integer_as_ast, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                      forall(member(Goal, [z3_ast_to_term(H, 12345, _), z3_ast_string(H, 12345, _)]))] ) :-
    catch(Goal, error(E, _), true),
    assertion(E == type_error(z3_ast, 12345)).

test(symbol_as_ast, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_symbol(H, a, S),
    catch(z3_ast_string(H, S, _), error(E, _), true),
    assertion(E == type_error(z3_ast, S)).

test(unbound_ast, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                   throws(error(instantiation_error, _))] ) :-
    z3_ast_to_term(H, _, _).

test(ast_wrong_handle, [setup((z3_new_handle(H1), z3_new_handle(H2))),
                        cleanup((z3_free_handle(H1), z3_free_handle(H2)))] ) :-
    term_to_z3_ast(H1, 1 + 2, A),
    catch(z3_ast_to_term(H2, A, _), error(E, _), true),
    assertion(E == permission_error(access, z3_ast, A)).

test(ast_after_free, [setup(z3_new_handle(H)), throws(error(existence_error(z3_handle, H), _))] ) :-
    term_to_z3_ast(H, 1 + 2, A),
    z3_free_handle(H),
    z3_ast_to_term(H, A, _).

repeated_symbol(H) :- z3_symbol(H, a, _), term_to_z3_ast(H, x > 1, _).

% Repeated objects reuse one blob; each blob must hold exactly one handle reference,
% or freeing and collecting below would release the handle too early or never.
test(repeated_objects_and_gc) :-
    z3_new_handle(H),
    forall(between(1, 1000, _), repeated_symbol(H)),
    z3_symbol(H, a, S),
    z3_free_handle(H),
    garbage_collect_atoms,
    assertion(blob(S, z3_symbol)),
    garbage_collect_atoms.

:- end_tests(object_blobs).
