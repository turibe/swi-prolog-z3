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
              z3_model_lists/3,            %% +handle, +model, -map: the same, for a given model
              z3_model_assocs/3,           %% +handle, +model, -map: with assocs, for a given model
              z3_model_assocs/2,           %% +handle, -map with assocs for constants and functions
              z3_reset_declarations/1,     %% +handle  Resets all declarations, does not clear solvers.
              z3_solver_assertions/2,      %% +handle, -assertions
              z3_check/2,                  %% +handle, -status
              z3_check_and_print/2,        %% +handle, -status  The same, printing a model if possible
              z3_set_timeout/2,            %% +handle, +milliseconds (0: no limit)
              z3_reason_unknown/2,         %% +handle, -reason for the last l_undef
              z3_interrupt/1,              %% +handle, from another thread
              z3_check_assumptions/3,      %% +handle, +literals, -status
              z3_get_unsat_core/2,         %% +handle, -literals
              z3_optimize/5,               %% +handle, +objectives, -status, -values, -model
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

%! z3_check(+Handle, -Status) is det.
%  Checks the assertions on Handle's solver; Status is `l_true`, `l_false` or `l_undef`.
%  The check can be interrupted: by a time limit (call_with_time_limit/2), thread_signal/2 or
%  Ctrl-C, which stop it and raise their exception, or by z3_interrupt/1, which makes it return
%  `l_undef`. A solver timeout (z3_set_timeout/2) also makes it return `l_undef`.
%  z3_check_and_print/2 can be interrupted in the same ways.
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

%! z3_solver_assertions(+Handle, -Assertions) is det.
%  Assertions is the formulas asserted on Handle's solver, newest first, converted back to Prolog with
%  the names z3_assert/2 accepts, so they can be asserted again.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_push(+Handle, -Scopes) is det.
%  Pushes a new scope on Handle's solver, and reports the new number of Scopes. z3_solver_pop/3 removes
%  the assertions made since.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_set_timeout(+Handle, +Milliseconds) is det.
%  Limits each check on Handle's solver to Milliseconds; a check that runs out returns `l_undef`,
%  with reason `timeout` or `canceled`, depending on which part of Z3 stops. 0 removes the limit.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_reason_unknown(+Handle, -Reason) is det.
%  Reason is an atom saying why the last check on Handle returned `l_undef`, such as `timeout`,
%  `interrupted` or `canceled`.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_interrupt(+Handle) is det.
%  Interrupts a check running on Handle, which then returns `l_undef` with reason `interrupted`.
%  Meant to be called from another thread; it does not wait for the handle, which is busy.
%  Does nothing if no check is running.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_check_assumptions(+Handle, +Assumptions, -Status) is det.
%  Checks Handle's solver under the extra Assumptions, for this check only. Assumptions is a list of
%  Boolean literals: Boolean constants such as `p:bool`, or their negations; anything else raises
%  `domain_error(boolean_literal, A)`. After `l_false`, z3_get_unsat_core/2 gives the assumptions used.
%  Interruptible, like z3_check/2.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_get_unsat_core(+Handle, -Core) is det.
%  After z3_check_assumptions/3 returned `l_false`, Core is the list of assumptions that its proof of
%  unsatisfiability used. Z3 keeps cores small, but they need not be minimal.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_optimize(+Handle, +Objectives, -Status, -Values, -Model) is det.
%  One-shot optimization over the assertions of Handle's solver, which is not changed.
%  Objectives is a list, in priority order (lexicographic), of `minimize(T)` and `maximize(T)` for an
%  arithmetic or bit-vector term T, and `soft(F)` and `soft(F, Weight)` for a formula F that should
%  hold, with a positive integer or float Weight (default 1). All soft constraints together form one
%  objective, at the position of the first one, minimizing the total weight of those violated.
%  After Status `l_true`, Values has one value per objective: the optimum of T, or for a soft
%  constraint whether it holds (`true` or `false`); and Model is a model, as from z3_get_model/2.
%  Otherwise Values is `[]` and Model is `none`. Optima can be infinite or not attained, so values
%  can contain `oo` (infinity) and `epsilon` (an infinitesimal): `-1*oo` for an unbounded minimum,
%  or `epsilon` for the infimum of x > 0. Interruptible, like z3_check/2, and uses the timeout set
%  with z3_set_timeout/2. Raises `domain_error(z3_objective, O)` for an objective of another form.
%  (Defined in `z3_swi_foreign.c`.)

%! z3_solver_pop(+Handle, +N, -Scopes) is det.
%  Pops Handle's solver `N` times, and reports the new number of Scopes.
%  Raises `domain_error(not_less_than_zero, N)` if N is negative, and
%  `domain_error(between(0, Current), N)` if N is more than the Current number of scopes;
%  the solver is unchanged in both cases.
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

%! z3_model_lists(+Handle, +Model, -Map) is det.
%  Like z3_model_lists/2, for a given Model of Handle, such as one from z3_get_model/2 or z3_optimize/5.
z3_model_lists(H, M, Map) :- z3_model_functions(H, M, F),
                             z3_model_constants(H, M, C),
                             sort(F, FS),
                             sort(C, CS),
                             Map = model{functions:FS, constants:CS}.


%! z3_model_assocs(+Handle, +Model, -Map) is det.
%  Like z3_model_assocs/2, for a given Model of Handle.
z3_model_assocs(H, M, Map) :- z3_model_functions(H, M, F),
                              z3_model_constants(H, M, C),
                              pair_list_to_assoc(F, Fmap),
                              pair_list_to_assoc(C, Cmap),
                              Map = model{functions:Fmap, constants:Cmap}.

%! z3_model_assocs(+Handle, -Model) is semidet.
%  Like z3_model_lists/2, with assoc maps instead of lists for the constants and functions.
z3_model_assocs(H, Model) :-
    must_be(ground, H),
    setup_call_cleanup(z3_get_model(H, M),
                       z3_model_assocs(H, M, Model),
                       z3_free_model(H, M)
                      ).


%! z3_model_lists(+Handle, -Model) is semidet.
%  Model is a model of the assertions on Handle's solver, after a check: the dict
%  `model{constants:Constants, functions:Functions}`. Constants is a list of `Name = Value`.
%  Functions is a list of `f(Args) = Value` for each point the model gives, and `(f/N = else) = Value`
%  for the other arguments; when that Value depends on the arguments, it is `lambda(Vars, Body)`,
%  with the arguments named as Z3 prints them: `lambda(['x!0':int], 'x!0' + 1)`. Values are numbers,
%  N/D for rationals, `true` and `false`, strings, enumeration values, `algebraic(Approx, Root)`
%  for irrational numbers, `fp_value(V, Sort)` for floating point, rounding modes such as `rne`,
%  and `store(...)` over `const_array(IndexSort, V)` for arrays. These can be given to Z3 again, with
%  the same meaning. Values of an uninterpreted sort are atoms such as `'foo!val!0'`, which name
%  distinct elements but, given to Z3 again, are read as new constants. Fails if there is no model
%  (no check yet, or status `l_false`).
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

%! z3_declarations(+Handle, -List) is det.
%  List is the constant and function declarations for Handle, as `(Name/Arity):Sort` terms.
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

test(solver_pop, [ setup(z3_new_handle(S)), cleanup(z3_free_handle(S)),
                   throws(error(domain_error(between(0, 1), 10), _)) ]) :-
    z3_solver_push(S, 1),
    z3_solver_pop(S, 10, _X).

% Popping more scopes than exist used to fail silently; now it raises, leaving the solver unchanged.
test(solver_pop_too_many_unchanged, [ setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_solver_push(S, 1),
    z3_assert(S, a:int > 1),
    z3_solver_push(S, 2),
    catch(z3_solver_pop(S, 3, _), E, true),
    assertion(E = error(domain_error(between(0, 2), 3), _)),
    z3_solver_scopes(S, N),
    assertion(N == 2),
    z3_solver_assertions(S, L),
    assertion(L == [a > 1]).

test(solver_pop_no_scopes, [ setup(z3_new_handle(S)), cleanup(z3_free_handle(S)),
                             throws(error(domain_error(between(0, 0), 1), _)) ]) :-
    z3_solver_pop(S, 1, _).

test(solver_pop_all, [ setup(z3_new_handle(S)), cleanup(z3_free_handle(S)) ]) :-
    z3_solver_push(S, _), z3_solver_push(S, _),
    z3_solver_pop(S, 2, N),            % exactly the number of scopes is fine
    assertion(N == 0),
    z3_solver_pop(S, 0, N0),           % and so is zero
    assertion(N0 == 0).

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

% pigeonhole(H, 9) is unsatisfiable and slow to prove (about 1.3 s on an M-series Mac),
% so it keeps the handle busy for a while.
:- use_module(examples/pigeonhole).

% A thread waiting for a busy handle used to ignore time limits and thread signals until the call
% holding the handle returned. Requires the pigeonhole check to outlast the waits (about 0.3 s).
test(interrupt_waiting_thread, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    pigeonhole(H, 9),
    thread_create(z3_check(H, _), Busy),
    sleep(0.1),
    thread_create(catch(z3_check(H, _), stop, true), Signalled),
    get_time(T0),
    catch(call_with_time_limit(0.2, z3_check(H, _)), E, true),
    get_time(T1),
    thread_signal(Signalled, throw(stop)),
    thread_join(Signalled, SignalledStatus),
    get_time(T2),
    assertion(thread_property(Busy, status(running))),   % both waits ended while it was busy
    thread_join(Busy, BusyStatus),
    assertion(E == time_limit_exceeded),
    assertion(T1 - T0 < 0.5),
    assertion(SignalledStatus == true),
    assertion(T2 - T1 < 0.3),
    assertion(BusyStatus == true),
    z3_solver_scopes(H, 0).                                % the handle still works

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

% z3_finalize_memory/0 frees memory every Z3 context needs, so it refuses while any exists.
% (z3.pl, loaded by the test suite, keeps a global handle, so finalizing always refuses here;
% make leaks exercises the successful case.)

:- begin_tests(finalize_memory).

live_handles(N) :-
    catch(z3_swi_foreign:z3_finalize_memory, error(permission_error(finalize, z3_memory, live_handles(N)), _), true),
    assertion(integer(N)).

test(refuses_with_live_handle, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    catch(z3_swi_foreign:z3_finalize_memory, E, true),
    assertion(E = error(permission_error(finalize, z3_memory, live_handles(_)), _)),
    z3_assert(H, a:int > 1),           % the handle still works
    z3_check(H, l_true).

test(counts_handles) :-
    garbage_collect_atoms,
    live_handles(N0),
    z3_new_handle(H),
    live_handles(N1),
    assertion(N1 =:= N0 + 1),
    z3_free_handle(H),
    live_handles(N2),
    assertion(N2 =:= N0).

unreferenced_handle :- z3_new_handle(_).

test(counts_until_collected) :-
    garbage_collect_atoms,
    live_handles(N0),
    unreferenced_handle,
    live_handles(N1),
    assertion(N1 =:= N0 + 1),          % still counted until garbage collected
    z3_new_handle(Flush), z3_free_handle(Flush),   % clears stale stack references (see test/leaks.pl)
    garbage_collect_atoms,
    live_handles(N2),
    assertion(N2 =:= N0).

:- end_tests(finalize_memory).

% Irrational values from nonlinear real arithmetic used to come back as the atom 'RootObject'.
% They are now algebraic(Approx, root(Coefficients, Index)): a float, and the exact value as
% the Index-th smallest real root of the polynomial with Coefficients, lowest degree first.

:- begin_tests(algebraic_numbers).

algebraic_model(Formulas, Constants) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( maplist(z3_assert(H), Formulas),
                         z3_check(H, l_true),
                         z3_model_lists(H, Model),
                         Constants = Model.constants ),
                       z3_free_handle(H)).

test(sqrt2_positive) :-
    algebraic_model([(x:real) * (x:real) = 2.0, (x:real) > 0.0], C),
    C = [x = algebraic(F, Root)],
    assertion(Root == root([-2, 0, 1], 2)),
    assertion(F =:= sqrt(2.0)).

test(sqrt2_negative) :-
    algebraic_model([(x:real) * (x:real) = 2.0, (x:real) < 0.0], C),
    C = [x = algebraic(F, Root)],
    assertion(Root == root([-2, 0, 1], 1)),
    assertion(F =:= -sqrt(2.0)).

test(cube_root) :-
    algebraic_model([(y:real) * (y:real) * (y:real) = 3.0], C),
    C = [y = algebraic(F, Root)],
    assertion(Root == root([-3, 0, 0, 1], 1)),
    assertion(abs(F - 3.0 ** (1/3)) < 1.0e-15).

% x^5 = x + 1 has a real root with no formula in radicals.
test(quintic) :-
    algebraic_model([(u:real) * (u:real) * (u:real) * (u:real) * (u:real) = (u:real) + 1.0], C),
    C = [u = algebraic(F, Root)],
    assertion(Root == root([-1, -1, 0, 0, 0, 1], 1)),
    assertion(abs(F ** 5 - F - 1) < 1.0e-12).

% Rational values in the same model are unchanged.
test(mixed_with_rational) :-
    algebraic_model([(z:real) * (z:real) = 2.0, (w:real) = (z:real) * (z:real)], C),
    assertion(memberchk(w = 2, C)),
    assertion(memberchk(z = algebraic(_, root([-2, 0, 1], _)), C)).   % either root of x^2 - 2

test(model_eval, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_assert(H, (x:real) * (x:real) = 2.0),
    z3_assert(H, (x:real) > 0.0),
    z3_check(H, l_true),
    z3_get_model(H, M),
    z3_model_eval(H, M, x, false, V),
    z3_free_model(H, M),
    V = algebraic(F, Root),
    assertion(Root == root([-2, 0, 1], 2)),
    assertion(F =:= sqrt(2.0)).

% Algebraic terms can also be given to Z3, as the exact root they denote; Approx is ignored.
test(round_trip, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    algebraic_model([(x:real) * (x:real) = 2.0, (x:real) > 0.0], [x = V]),
    z3_assert(H, (y:real) = V),
    z3_solver_push(H, _),
    z3_assert(H, (y:real) * (y:real) = 2.0),
    z3_check(H, l_true),
    z3_solver_pop(H, 1, _),
    z3_assert(H, (y:real) > 1.5),
    z3_check(H, l_false).

test(simplify_product, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))] ) :-
    z3_simplify(H, algebraic(0.0, root([-2, 0, 1], 2)) * algebraic(0.0, root([-2, 0, 1], 2)), S),
    assertion(S =:= 2).

denoted(algebraic(0.0, root([-2, 0, 1], 1)), (w:real) < 0.0).            % the smaller root
denoted(algebraic(0.0, root([-1, -1, 0, 0, 0, 1], 1)), (w:real) > 1.16). % the real root of x^5 - x - 1
denoted(algebraic(0.0, root([-1, 2], 1)), (w:real) = 0.5).               % a rational root

test(denotes_root, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                    forall(denoted(A, Property))] ) :-
    z3_assert(H, (w:real) = A),
    z3_assert(H, not(Property)),
    z3_check(H, l_false).

% Like other malformed values in a formula, these fail.
malformed_algebraic(algebraic(0.0, root([-2, 0, 1], 3))).   % x^2 - 2 has only 2 real roots
malformed_algebraic(algebraic(0.0, root([-2, 0, 1], 0))).   % roots count from 1
malformed_algebraic(algebraic(0.0, root([-2, 0, 0], 1))).   % leading coefficient zero
malformed_algebraic(algebraic(0.0, root([-2, x, 1], 1))).   % non-integer coefficient
malformed_algebraic(algebraic(0.0, root([1], 1))).          % constant polynomial
malformed_algebraic(algebraic(foo, root([-2, 0, 1], 1))).   % approximation not a number

test(malformed, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                 forall(malformed_algebraic(A))] ) :-
    \+ z3_assert(H, (w:real) = A).

:- end_tests(algebraic_numbers).

% The string sort and string operations (named str_..., argument orders as in SMT-LIB).
% Type annotations are parenthesized, so these tests do not depend on z3.pl's op(299, xfy, :).

:- begin_tests(strings).

% Formula holds whenever the string w is "hello": asserting its negation is unsatisfiable.
hello_implies(Formula) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( z3_assert(H, (w:string) = "hello"),
                         z3_assert(H, not(Formula)),
                         z3_check(H, l_false) ),
                       z3_free_handle(H)).

string_fact(str_len(w) = 5).
string_fact(str_concat(w, " ", "world") = "hello world").
string_fact(str_at(w, 1) = "e").
string_fact(str_substr(w, 1, 3) = "ell").
string_fact(str_contains(w, "ell")).
string_fact(not(str_contains(w, "z"))).
string_fact(str_prefixof("he", w)).
string_fact(str_suffixof("lo", w)).
string_fact(str_indexof(w, "l", 0) = 2).
string_fact(str_indexof(w, "l", 3) = 3).
string_fact(str_indexof(w, "z", 0) = -1).
string_fact(str_replace(w, "l", "L") = "heLlo").           % the first occurrence only
string_fact(str_lt("abc", w)).
string_fact(str_le(w, w)).
string_fact(not(str_lt(w, w))).
string_fact(str_to_int("123") = 123).
string_fact(str_to_int("12a") = -1).
string_fact(int_to_str(42) = "42").
string_fact(int_to_str(-1) = "").

test(operations, [forall(string_fact(F))]) :-
    hello_implies(F).

string_model(Formulas, Constants) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( maplist(z3_assert(H), Formulas),
                         z3_check(H, l_true),
                         z3_model_lists(H, Model),
                         Constants = Model.constants ),
                       z3_free_handle(H)).

test(solve_for_strings) :-
    string_model([(s:string) = str_concat("ab", t:string), str_len(s:string) = 5, str_contains(s:string, "bc")], C),
    memberchk(s = S, C), memberchk(t = T, C),
    assertion(string_concat("ab", T, S)),
    assertion(string_length(S, 5)),
    assertion(sub_string(S, _, _, _, "bc")).

test(solve_through_int_conversion) :-
    string_model([str_to_int(x:string) = 7, str_len(x:string) = 3], C),
    assertion(C == [x = "007"]).

% Strings go to Z3 and back by code point: non-ASCII characters, and backslashes, which
% Z3_mk_string would read as the start of an escape such as \u{41}, are kept exactly.
test(round_trip_exact, [forall(member(Text, ["héllo wörld ✓", "back\\slash \\u{41} tab\t", ""]))]) :-
    string_model([(u:string) = Text], C),
    assertion(C == [u = Text]).

test(length_in_code_points) :-
    string_model([(u:string) = "héllo ✓", str_len(u:string) = n:int], C),
    assertion(memberchk(n = 7, C)).

% Terms come back with the Prolog names, not Z3's str.len and so on, so they can be asserted again.
test(names_round_trip, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_simplify(H, str_len(str_concat("ab", y:string)), S),
    assertion(S == 2 + str_len(y)),
    Formula = str_prefixof("p", str_replace(y:string, "a", int_to_str(str_to_int(y:string)))),
    z3_assert(H, Formula),
    z3_solver_assertions(H, [Back]),
    assertion(Back == str_prefixof("p", str_replace(y, "a", int_to_str(str_to_int(y))))),
    z3_assert(H, Back).

malformed_string_formula(str_len(w:string, w:string) = 1).   % wrong arity
malformed_string_formula(str_len(3) = 1).                    % not a string
malformed_string_formula((w:string) = 3).                    % sort mismatch

test(malformed, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                 forall(malformed_string_formula(F))]) :-
    \+ z3_assert(H, F).

:- end_tests(strings).

% Stopping a running check: a time limit, a thread signal, a solver timeout, or z3_interrupt/1.
% pigeonhole(H, 9) takes about 1.3 s to prove unsatisfiable, so it is still running when stopped.

:- begin_tests(interrupts).

:- use_module(examples/pigeonhole).

busy_handle(H) :- z3_new_handle(H), pigeonhole(H, 9).

elapsed(Goal, Seconds) :- get_time(T0), call(Goal), get_time(T1), Seconds is T1 - T0.

% A running check used to see Prolog signals only after Z3 returned.
test(time_limit, [setup(busy_handle(H)), cleanup(z3_free_handle(H))]) :-
    elapsed(catch(call_with_time_limit(0.2, z3_check(H, _)), E, true), Seconds),
    assertion(E == time_limit_exceeded),
    assertion(Seconds < 0.6),
    z3_solver_scopes(H, 0).                                 % the handle still works

test(thread_signal, [setup(busy_handle(H)), cleanup(z3_free_handle(H))]) :-
    thread_self(Me),
    thread_create(( sleep(0.1), thread_signal(Me, throw(stop)) ), Signaller),
    elapsed(catch(z3_check(H, _), Caught, true), Seconds),
    thread_join(Signaller, _),
    assertion(Caught == stop),
    assertion(Seconds < 0.6).

test(z3_interrupt, [setup(busy_handle(H)), cleanup(z3_free_handle(H))]) :-
    thread_create(( sleep(0.1), z3_interrupt(H) ), Interrupter),
    elapsed(z3_check(H, Status), Seconds),
    thread_join(Interrupter, _),
    assertion(Status == l_undef),
    z3_reason_unknown(H, Reason),
    assertion(Reason == interrupted),
    assertion(Seconds < 0.6).

% pigeonhole(H, 8) takes about 0.1 s, far longer than a 1 ms timeout.
test(timeout, [setup((z3_new_handle(H), pigeonhole(H, 8))), cleanup(z3_free_handle(H))]) :-
    z3_set_timeout(H, 1),
    z3_check(H, Status),
    assertion(Status == l_undef),
    z3_reason_unknown(H, Reason),
    assertion(memberchk(Reason, [timeout, canceled])),   % depends on which part of Z3 stops
    z3_set_timeout(H, 0),                                   % no limit again
    z3_check(H, Status2),
    assertion(Status2 == l_false).

test(interrupt_while_idle, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_interrupt(H),                                        % no check running: no effect
    z3_assert(H, (x:int) > 1),
    z3_check(H, l_true).

test(timeout_errors, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)),
                      forall(member(Ms-Error, [-1-domain_error(between(0, 4294967294), -1),
                                               foo-type_error(integer, foo)]))]) :-
    catch(z3_set_timeout(H, Ms), error(E, _), true),
    assertion(E == Error).

test(interrupt_errors) :-
    catch(z3_interrupt(12345), error(E1, _), true),
    assertion(E1 == type_error(z3_handle, 12345)),
    z3_new_handle(H),
    z3_free_handle(H),
    catch(z3_interrupt(H), error(E2, _), true),
    assertion(E2 = existence_error(z3_handle, _)).

:- end_tests(interrupts).

% Checking under assumptions, and unsat cores.

:- begin_tests(unsat_cores).

:- use_module(examples/pigeonhole).

tracked(H) :-
    z3_new_handle(H),
    z3_assert(H, implies(p:bool, (x:int) > 3)),
    z3_assert(H, implies(q:bool, (x:int) < 2)),
    z3_assert(H, implies(r:bool, (y:int) = 1)).

test(core, [setup(tracked(H)), cleanup(z3_free_handle(H))]) :-
    z3_check_assumptions(H, [p, q, r], Status),
    assertion(Status == l_false),
    z3_get_unsat_core(H, Core),
    msort(Core, Sorted),
    assertion(Sorted == [p, q]).                            % r is not needed

test(negated_assumption, [setup(tracked(H)), cleanup(z3_free_handle(H))]) :-
    z3_check_assumptions(H, [p, not(q), r], Status),
    assertion(Status == l_true).

test(assumptions_are_temporary, [setup(tracked(H)), cleanup(z3_free_handle(H))]) :-
    z3_check_assumptions(H, [p, q], l_false),
    z3_check(H, Status),                                    % without them, satisfiable again
    assertion(Status == l_true).

test(no_assumptions, [setup(tracked(H)), cleanup(z3_free_handle(H))]) :-
    z3_check_assumptions(H, [], Status),
    assertion(Status == l_true).

test(not_literals, [setup(tracked(H)), cleanup(z3_free_handle(H)),
                    forall(member(A, [(x:int) > 3, undeclared_atom, and(p, q)]))]) :-
    catch(z3_check_assumptions(H, [A], _), error(E, _), true),
    assertion(E == domain_error(boolean_literal, A)).

test(bad_lists, [setup(tracked(H)), cleanup(z3_free_handle(H)),
                 forall(member(L-Error, [[p|_]-instantiation_error, foo-type_error(list, foo)]))]) :-
    catch(z3_check_assumptions(H, L, _), error(E, _), true),
    assertion(E =@= Error).

% Interruptible, like z3_check.
test(time_limit, [setup((z3_new_handle(H), pigeonhole(H, 9), z3_assert(H, implies(s:bool, true)))),
                  cleanup(z3_free_handle(H))]) :-
    get_time(T0),
    catch(call_with_time_limit(0.2, z3_check_assumptions(H, [s], _)), E, true),
    get_time(T1),
    assertion(E == time_limit_exceeded),
    assertion(T1 - T0 < 0.6).

:- end_tests(unsat_cores).

% One-shot optimization (z3_optimize/5).

:- begin_tests(optimization).

:- use_module(examples/pigeonhole).

% Optimizes Objectives subject to Formulas; Constants are the model's constants.
optimize(Formulas, Objectives, Status, Values, Constants) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( maplist(z3_assert(H), Formulas),
                         z3_optimize(H, Objectives, Status, Values, M),
                         ( M == none -> Constants = none ; z3_model_lists(H, M, Model), Constants = Model.constants ) ),
                       z3_free_handle(H)).

box([(x:int) >= 0, (y:int) >= 0, (x:int) + (y:int) =< 10]).

test(maximize) :-
    box(B),
    optimize(B, [maximize(2*x + y)], Status, Values, C),
    assertion(Status == l_true),
    assertion(Values == [20]),
    assertion(C == [x = 10, y = 0]).

% Objectives are lexicographic: earlier ones take priority.
test(priority_order, [forall(member(Os-Expected, [[maximize(x), maximize(y)]-[x = 10, y = 0],
                                                    [maximize(y), maximize(x)]-[x = 0, y = 10]]))]) :-
    box(B),
    optimize(B, Os, l_true, _, C),
    assertion(C == Expected).

test(soft_weights, [forall(member(Os-Values-Expected, [[soft(p, 2), soft(q)]-[true, false]-[p = true, q = false],
                                                         [soft(p, 0.5), soft(q, 1.5)]-[false, true]-[p = false, q = true]]))]) :-
    optimize([not(and(p:bool, q:bool))], Os, l_true, Vs, C),
    assertion(Vs == Values),
    assertion(C == Expected).

test(infinite_and_infinitesimal, [forall(member(Fs-O-Value, [[(x:int) > 0]-maximize(x)-oo,
                                                               [(x:int) < 0]-minimize(x)-(-1*oo),
                                                               [(x:real) > 0.0]-minimize(x)-epsilon]))]) :-
    optimize(Fs, [O], l_true, [V], _),
    assertion(V == Value).

test(bit_vectors) :-
    optimize([(b:bv(8)) = b], [maximize(b)], l_true, Values, _),
    assertion(Values == [255]).

test(unsatisfiable) :-
    optimize([(x:int) > 0, (x:int) < 0], [maximize(x)], Status, Values, C),
    assertion(Status == l_false),
    assertion(Values == []),
    assertion(C == none).

test(solver_unchanged, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_assert(H, (x:int) > 0),
    z3_optimize(H, [maximize(x), soft((x:int) < 5)], _, _, _),
    z3_solver_assertions(H, As),
    assertion(As == [x > 0]),
    z3_check(H, l_true).

% pigeonhole(H, 9) takes about 1.3 s even without objectives.
test(timeout, [setup((z3_new_handle(H), pigeonhole(H, 9))), cleanup(z3_free_handle(H))]) :-
    z3_set_timeout(H, 50),
    z3_optimize(H, [soft(p_1_1:bool)], Status, Values, M),
    assertion(Status == l_undef),
    assertion(Values == []),
    assertion(M == none).

test(time_limit, [setup((z3_new_handle(H), pigeonhole(H, 9))), cleanup(z3_free_handle(H))]) :-
    get_time(T0),
    catch(call_with_time_limit(0.2, z3_optimize(H, [soft(p_1_1:bool)], _, _, _)), E, true),
    get_time(T1),
    assertion(E == time_limit_exceeded),
    assertion(T1 - T0 < 0.6).

bad_objective([foo(x)], domain_error(z3_objective, foo(x))).
bad_objective([soft(p:bool, -1)], domain_error(positive_number, -1)).
bad_objective([soft(p:bool, 0)], domain_error(positive_number, 0)).
bad_objective([soft(p:bool, foo)], type_error(number, foo)).
bad_objective(not_a_list, type_error(list, not_a_list)).

test(errors, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), forall(bad_objective(Os, Error))]) :-
    catch(z3_optimize(H, Os, _, _, _), error(E, _), true),
    assertion(E == Error).

test(not_a_number_objective, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), fail]) :-
    z3_optimize(H, [maximize(p:bool)], _, _, _).

:- end_tests(optimization).

% Arrays: the sort array(IndexSort, ValueSort), with select/2, store/3 and const_array/2.

:- begin_tests(arrays).

array_model(Formulas, Constants) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( maplist(z3_assert(H), Formulas),
                         z3_check(H, l_true),
                         z3_model_lists(H, Model),
                         Constants = Model.constants ),
                       z3_free_handle(H)).

% Formula holds given Assumptions: asserting its negation is unsatisfiable.
holds(Assumptions, Formula) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( maplist(z3_assert(H), Assumptions),
                         z3_assert(H, not(Formula)),
                         z3_check(H, l_false) ),
                       z3_free_handle(H)).

% Model values are store chains over a constant array, as Z3 gives them.
test(model_value) :-
    array_model([select(a:array(int, int), 1) = 5, select(a:array(int, int), 2) = 7], C),
    C = [a = V],
    assertion(V = store(const_array(int, _), _, _)).

% A model value can be given back to Z3.
test(model_value_round_trip) :-
    array_model([select(a:array(int, int), 1) = 5, select(a:array(int, int), 2) = 7], [a = V]),
    holds([(b:array(int, int)) = V], and(select(b:array(int, int), 1) = 5, select(b:array(int, int), 2) = 7)).

array_fact(select(store(c:array(int, int), 1, 10), 1) = 10).
array_fact(select(store(c:array(int, int), 1, 10), 2) = select(c:array(int, int), 2)).
array_fact(select(const_array(int, 0), 42) = 0).
array_fact(store(store(c:array(int, int), 1, 5), 1, 6) = store(c:array(int, int), 1, 6)).
array_fact(select(select(store(const_array(int, const_array(int, 0)), 1, store(const_array(int, 0), 2, 3)), 1), 2) = 3).

test(operations, [forall(array_fact(F))]) :-
    holds([], F).

test(extensionality) :-
    holds([(a:array(int, int)) = b:array(int, int), select(a:array(int, int), 1) = 1],
          select(b:array(int, int), 1) = 1).

array_sort_model([select(p:array(int, bool), 0), not(select(p:array(int, bool), 1))], p, store(const_array(int, false), 0, true)).
array_sort_model([(r:array(int, real)) = const_array(int, 1.5)], r, const_array(int, 3/2)).
array_sort_model([select(s:array(int, string), 0) = "zero"], s, const_array(int, "zero")).
array_sort_model([select(v:array(bv(4), bv(4)), int2bv(4, 1)) = int2bv(4, 9)], v, const_array(bv(4), 9)).
array_sort_model([select(select(g:array(int, array(int, int)), 1), 2) = 3], g, const_array(int, const_array(int, 3))).

test(other_sorts, [forall(array_sort_model(Formulas, Name, Expected))]) :-
    array_model(Formulas, C),
    assertion(memberchk(Name = Expected, C)).

test(declarations, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_declare_function(H, d, array(int, array(int, real))),
    z3_declarations(H, Ds),
    assertion(Ds == [(d/0):array('Int', array('Int', 'Real'))]).

% Simplified terms keep the Prolog names, so they can be asserted again.
test(simplify, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_simplify(H, select(store(const_array(int, 0), 1, 5), 1), S1),
    assertion(S1 == 5),
    z3_simplify(H, store(store(const_array(int, 0), 1, 5), 1, 6), S2),
    assertion(S2 == store(const_array(int, 0), 1, 6)),
    z3_assert(H, (e:array(int, int)) = S2),
    z3_check(H, l_true).

malformed_array_formula(select(a:array(int, int)) = 1).                   % wrong arity
malformed_array_formula(select(a:array(int, int), "x") = 1).              % index of the wrong sort
malformed_array_formula(store(a:array(int, int), 1, "y") = a:array(int, int)). % value of the wrong sort
malformed_array_formula(select(n:int, 1) = 2).                            % not an array
malformed_array_formula(select(const_array(f(x), 0), 1) = 0).             % not a sort

test(malformed, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H)), forall(malformed_array_formula(F))]) :-
    \+ z3_assert(H, F).

:- end_tests(arrays).

% Quantifiers: forall(Vars, Body) and exists(Vars, Body), with Vars a list of Name:Sort.
% Z3 decides satisfiable quantified formulas only sometimes, so each handle has a timeout.

:- begin_tests(quantifiers).

quantified_handle(H) :- z3_new_handle(H), z3_set_timeout(H, 2000).

status_of(Formulas, Status) :-
    setup_call_cleanup(quantified_handle(H),
                       ( maplist(z3_assert(H), Formulas), z3_check(H, Status) ),
                       z3_free_handle(H)).

% Formula follows from Assumptions: asserting its negation is unsatisfiable.
follows(Decls, Assumptions, Formula) :-
    setup_call_cleanup(quantified_handle(H),
                       ( forall(member(D-T, Decls), z3_declare_function(H, D, T)),
                         maplist(z3_assert(H), Assumptions),
                         z3_assert(H, not(Formula)),
                         z3_check(H, l_false) ),
                       z3_free_handle(H)).

quantified_status(forall([x:int], (x:int) + 0 = x), l_true).
quantified_status(forall([x:int], x > 0), l_false).
quantified_status(exists([x:int], x * x = 4), l_true).
quantified_status(exists([x:int], x * x = 2), l_false).
quantified_status(forall([x:int], exists([y:int], y > x)), l_true).
quantified_status(forall([x:int], exists([x:int], x > 5)), l_true).   % the inner x shadows the outer one

test(status, [forall(quantified_status(F, Expected))]) :-
    status_of([F], Status),
    assertion(Status == Expected).

test(instantiation, [forall(member(Decls-As-F, [ [f(int)-int]-[forall([x:int], f(x) > x)]-(f(3) > 3),
                                                 [f(int)-int]-[forall([x:int], f(x) = 2 * x)]-(f(5) = 10),
                                                 [g(int, int)-int]-[forall([x:int, y:int], g(x, y) = g(y, x))]-(g(1, 2) = g(2, 1)) ]))]) :-
    follows(Decls, As, F).

% A bound variable shadows a constant of the same name, of any sort; other constants are global.
test(shadowing, [setup(quantified_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_declare_function(H, x, bool),
    z3_assert(H, x),
    z3_assert(H, forall([x:int], x * 0 = 0)),
    z3_check(H, l_true).

test(global_inside_body) :-
    follows([h(int)-int], [(z:int) = 7, forall([y:int], h(y) > z)], h(0) > 7).

% x:Sort inside the body refers to the bound variable if the sort is the same.
test(annotated_inside_body) :-
    status_of([forall([x:int], (x:int) * 0 = 0)], l_true).

test(annotated_inside_body_other_sort, [setup(quantified_handle(H)), cleanup(z3_free_handle(H)), fail]) :-
    z3_assert(H, forall([x:int], (x:bool))).

% Assertions come back as forall/exists terms, which can be asserted again.
test(round_trip, [setup(quantified_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_declare_function(H, f(int), int),
    F = forall([x:int], exists([y:real], f(x) > x or y > x)),
    z3_assert(H, F),
    z3_solver_assertions(H, [Back]),
    % Z3 converts x to a real to compare it with y, so Back has int2real(x) (Z3's to_real).
    assertion(Back == forall([x:int], exists([y:real], f(x) > x or y > int2real(x)))),
    z3_assert(H, Back).

malformed_quantifier(forall([], p:bool)).            % no bound variables
malformed_quantifier(forall([x], x > 0)).            % no sort (z3.pl infers sorts; this level needs them)
malformed_quantifier(forall([x:int], x + 1)).        % body not a formula
malformed_quantifier(forall(x:int, x > 0)).          % not a list
malformed_quantifier(exists([x:foo(bar)], true)).    % not a sort

test(malformed, [setup(quantified_handle(H)), cleanup(z3_free_handle(H)), forall(malformed_quantifier(F))]) :-
    \+ z3_assert(H, F).

% Z3 cannot decide this satisfiable formula (it would need f(x) = x + 1); a time limit stops the check.
test(undecided_can_be_interrupted, [setup(z3_new_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_declare_function(H, f(int), int),
    z3_assert(H, forall([x:int], f(x) > x)),
    get_time(T0),
    catch(call_with_time_limit(0.3, z3_check(H, _)), E, true),
    get_time(T1),
    assertion(E == time_limit_exceeded),
    assertion(T1 - T0 < 1.0).

% Not only in quantifiers: the conversions Z3 inserts when integers and reals are mixed come back
% with the Prolog names, so the terms can be asserted again.
test(mixed_arithmetic_round_trip, [setup(quantified_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_assert(H, (y:real) > (x:int)),
    z3_assert(H, is_int(y:real)),
    z3_solver_assertions(H, As),
    assertion(As == [is_int(y), y > int2real(x)]),
    forall(member(A, As), z3_assert(H, A)),
    z3_check(H, l_true).

:- end_tests(quantifiers).

% Division with one integer and one real argument is real division. (Z3_mk_div used to divide as
% integers when the first argument was an integer, truncating the second: x / 2.0 was 1 for x = 3.)

:- begin_tests(mixed_division).

division_value(Formula, Value) :-
    setup_call_cleanup(( z3_new_handle(H),
                         z3_declare_function(H, x, int),
                         z3_declare_function(H, r, real),
                         z3_declare_function(H, v, real) ),
                       ( z3_assert(H, x = 3), z3_assert(H, r = 2.0), z3_assert(H, v = Formula),
                         z3_check(H, l_true),
                         z3_model_lists(H, M),
                         memberchk(v = Value, M.constants) ),
                       z3_free_handle(H)).

test(real_division, [forall(member(F-V, [x / 2.0 - 3/2, 3 / 2.0 - 3/2, x / r - 3/2, div(x, 2.0) - 3/2,
                                          r / x - 2/3, 1.5 / x - 1/2]))]) :-
    division_value(F, Value),
    assertion(Value == V).

% Two integers still divide as integers.
test(integer_division) :-
    division_value(x / 2, Value),
    assertion(Value == 1).

:- end_tests(mixed_division).

% IEEE floating point at the low level: sorts, values, operations and conversions.

:- begin_tests(floating_point).

fp_handle(H) :-
    z3_new_handle(H),
    forall(member(N:S, [x:float32, y:float32, d:float64, q:float128, h:float16, c:fp(4, 6),
                        m:roundingmode, b:bv(8), w:bv(32)]),
           z3_declare_function(H, N, S)).

% The value of constant Name in a model of Formulas.
fp_model_value(Formulas, Name, Value) :-
    setup_call_cleanup(fp_handle(H),
                       ( forall(member(F, Formulas), z3_assert(H, F)),
                         z3_check(H, l_true),
                         z3_model_lists(H, M),
                         memberchk(Name = Value, M.constants) ),
                       z3_free_handle(H)).

% Formula holds whenever Facts do: asserting its negation is unsatisfiable.
fp_implied(Facts, Formula) :-
    setup_call_cleanup(fp_handle(H),
                       ( forall(member(F, Facts), z3_assert(H, F)),
                         z3_assert(H, not(Formula)),
                         z3_check(H, l_false) ),
                       z3_free_handle(H)).

test(sorts) :-
    setup_call_cleanup(fp_handle(H), z3_declarations(H, Ds), z3_free_handle(H)),
    forall(member(N-S, [x-float32, d-float64, q-float128, h-float16, c-fp(4, 6), m-roundingmode]),
           assertion(memberchk((N/0):S, Ds))).

% float and double once meant real: now neither is a sort.
test(float_double_not_sorts, [forall(member(S, [float, double]))]) :-
    setup_call_cleanup(z3_new_handle(H),
                       assertion(\+ catch(z3_declare_function(H, z, S), _, fail)),
                       z3_free_handle(H)).

test(bad_fp_widths, [fail]) :-
    setup_call_cleanup(z3_new_handle(H), z3_declare_function(H, z, fp(1, 2)), z3_free_handle(H)).

% Values, special ones included, come back as fp_value(Value, Sort).
fp_value_case([fp_is_nan(x)], x, fp_value(nan, float32)).
fp_value_case([x = fp_value(-inf, float32)], x, fp_value(-inf, float32)).
fp_value_case([x = fp_value(inf, float32)], x, fp_value(inf, float32)).
fp_value_case([fp_is_zero(x), fp_is_negative(x)], x, fp_value(-0.0, float32)).
fp_value_case([x = fp_value(1.5, float32)], x, fp_value(1.5, float32)).
fp_value_case([h = fp_div(rne, fp_value(1, float16), fp_value(3, float16))], h, fp_value(0.333251953125, float16)).
fp_value_case([c = fp_value(1.5, fp(4, 6))], c, fp_value(1.5, fp(4, 6))).
fp_value_case([fp_is_subnormal(d), fp_is_positive(d), fp_lt(d, fp_value(1.0e-323, float64))], d, fp_value(5.0e-324, float64)).
fp_value_case([m = rtp], m, rtp).

test(values, [forall(fp_value_case(Formulas, Name, Expected))]) :-
    fp_model_value(Formulas, Name, Value),
    assertion(Value == Expected).

% fp_value(V, Sort) rounds V to the nearest value of Sort: 0.1 as a float32 is not 0.1 as a double.
test(nearest_value) :-
    fp_model_value([x = fp_value(0.1, float32)], x, fp_value(V, float32)),
    assertion(V =:= 0.100000001490116119384765625).

% Formats larger than a double give exact integers or rationals.
test(float128_exact) :-
    fp_model_value([q = fp_div(rne, fp_value(1, float128), fp_value(3, float128))], q, fp_value(V, float128)),
    assertion(rational(V)),
    assertion(abs(V - 1r3) < 1r10000000000000000000000000000000000).

% Values from models can be asserted again, with the same meaning.
test(round_trip, [forall(member(F, [fp_add(rne, x, fp_value(0.1, float32)) = fp_value(0.3, float32),
                                     fp_is_nan(x), fp_is_subnormal(x), fp_is_zero(x) and fp_is_negative(x)]))]) :-
    fp_model_value([F], x, V),
    assertion(fp_implied([x = V], F)).

test(float128_round_trip) :-
    Q = fp_div(rne, fp_value(1, float128), fp_value(3, float128)),
    fp_model_value([q = Q], q, V),
    assertion(fp_implied([q = V], q = Q)).

% IEEE equality (fp_eq) is not structural equality (=): NaN is not fp_eq to itself, and the two
% zeros are fp_eq but not =.
test(fp_eq_vs_equality) :-
    assertion(fp_implied([fp_is_nan(x)], not(fp_eq(x, x)))),
    assertion(fp_implied([fp_is_nan(x)], x = x)),
    assertion(fp_implied([], fp_eq(fp_value(0.0, float32), fp_value(-0.0, float32)))),
    assertion(fp_implied([], not(fp_value(0.0, float32) = fp_value(-0.0, float32)))).

fp_fact(fp_eq(fp_add(rne, fp_value(1, float32), fp_value(2, float32)), fp_value(3, float32))).
fp_fact(fp_eq(fp_sub(rne, fp_value(1, float32), fp_value(2, float32)), fp_value(-1, float32))).
fp_fact(fp_eq(fp_mul(rne, fp_value(3, float32), fp_value(2, float32)), fp_value(6, float32))).
fp_fact(fp_eq(fp_div(rne, fp_value(1, float32), fp_value(4, float32)), fp_value(0.25, float32))).
fp_fact(fp_eq(fp_fma(rne, fp_value(2, float32), fp_value(3, float32), fp_value(1, float32)), fp_value(7, float32))).
fp_fact(fp_eq(fp_sqrt(rne, fp_value(9, float32)), fp_value(3, float32))).
fp_fact(fp_eq(fp_rem(fp_value(7, float32), fp_value(4, float32)), fp_value(-1, float32))).   % IEEE remainder
fp_fact(fp_eq(fp_round_to_integral(rtz, fp_value(2.7, float32)), fp_value(2, float32))).
fp_fact(fp_eq(fp_round_to_integral(rne, fp_value(2.5, float32)), fp_value(2, float32))).   % ties to even
fp_fact(fp_eq(fp_round_to_integral(rna, fp_value(2.5, float32)), fp_value(3, float32))).
fp_fact(fp_eq(fp_abs(fp_value(-2, float32)), fp_value(2, float32))).
fp_fact(fp_eq(fp_neg(fp_value(2, float32)), fp_value(-2, float32))).
fp_fact(fp_eq(fp_min(fp_value(1, float32), fp_value(2, float32)), fp_value(1, float32))).
fp_fact(fp_eq(fp_max(fp_value(1, float32), fp_value(2, float32)), fp_value(2, float32))).
fp_fact(fp_lt(fp_value(1, float32), fp_value(2, float32))).
fp_fact(fp_leq(fp_value(2, float32), fp_value(2, float32))).
fp_fact(fp_gt(fp_value(inf, float32), fp_value(1.0e38, float32))).
fp_fact(fp_geq(fp_value(2, float32), fp_value(-inf, float32))).
fp_fact(not(fp_lt(fp_value(nan, float32), fp_value(1, float32)))).      % NaN is unordered
fp_fact(fp_is_normal(fp_value(1, float32))).
fp_fact(fp_is_subnormal(fp_value(1.0e-40, float32))).
fp_fact(fp_is_infinite(fp_mul(rne, fp_value(1.0e38, float32), fp_value(10, float32)))). % overflow
fp_fact(fp_is_zero(fp_value(1.0e-50, float32))).                         % underflow
fp_fact(fp_is_positive(fp_value(1, float32))).
fp_fact(fp_is_negative(fp_value(-1, float32))).
fp_fact(fp_to_real(fp_value(0.5, float32)) = 1r2).
fp_fact(fp_eq(to_fp(rne, 3, float32), fp_value(3, float32))).
fp_fact(fp_eq(to_fp(rne, fp_value(0.5, float64), float32), fp_value(0.5, float32))).
fp_fact(fp_eq(to_fp(rne, int2bv(8, -3), float32), fp_value(-3, float32))).          % signed
fp_fact(fp_eq(to_fp_unsigned(rne, int2bv(8, -3), float32), fp_value(253, float32))). % unsigned
fp_fact(fp_to_sbv(rtz, fp_value(-7.9, float32), 8) = int2bv(8, -7)).
fp_fact(fp_to_ubv(rtz, fp_value(7.9, float32), 8) = int2bv(8, 7)).
fp_fact(fp_to_ieee_bv(fp_value(1, float32)) = int2bv(32, 1065353216)).
fp_fact(fp_eq(fp_from_ieee_bv(int2bv(32, 1065353216), float32), fp_value(1, float32))).

test(operations, [forall(fp_fact(F))]) :-
    assertion(fp_implied([], F)).

% The rounding mode matters: 1 + 2^-30 is 1 to nearest, but not toward positive infinity.
test(rounding_modes) :-
    Tiny = fp_value(9.313225746154785e-10, float32),
    assertion(fp_implied([], fp_add(rne, fp_value(1, float32), Tiny) = fp_value(1, float32))),
    assertion(fp_implied([], fp_gt(fp_add(rtp, fp_value(1, float32), Tiny), fp_value(1, float32)))).

% Floating-point addition is commutative (with =; with fp_eq, NaN breaks it), but not associative.
test(commutative_not_associative) :-
    assertion(fp_implied([], fp_add(rne, x, y) = fp_add(rne, y, x))),
    assertion(\+ fp_implied([], fp_add(rne, fp_add(rne, h, h), fp_value(1, float16))
                                 = fp_add(rne, h, fp_add(rne, h, fp_value(1, float16))))).

% Assertions with floating-point terms come back with the Prolog names, so they can be asserted again.
test(assertions_round_trip, [setup(fp_handle(H)), cleanup(z3_free_handle(H))]) :-
    z3_assert(H, fp_lt(fp_add(rne, x, fp_value(0.5, float32)), y)),
    z3_assert(H, w = fp_to_sbv(rtz, to_fp(rne, d, float32), 32)),
    z3_assert(H, fp_eq(to_fp_unsigned(rtn, b, float32), fp_from_ieee_bv(w, float32))),
    z3_solver_assertions(H, As),                                % newest first
    assertion(As == [fp_eq(to_fp_unsigned(rtn, b, float32), fp_from_ieee_bv(w, float32)),
                     w = fp_to_sbv(rtz, to_fp(rne, d, float32), 32),
                     fp_lt(fp_add(rne, x, fp_value(0.5, float32)), y)]),
    forall(member(A, As), z3_assert(H, A)),
    z3_check(H, l_true).

bad_fp_formula(fp_add(rne, x, d)).               % different formats
bad_fp_formula(fp_value(1.0, real) = x).          % not a floating-point sort
bad_fp_formula(fp_value(foo, float32) = x).       % not a value
bad_fp_formula(x = to_fp(rne, "s", float32)).     % not convertible
bad_fp_formula(b = fp_to_sbv(rtz, x, 0)).         % no bits

test(bad_formulas, [forall(bad_fp_formula(F))]) :-
    setup_call_cleanup(fp_handle(H),
                       assertion(\+ z3_assert(H, F)),
                       z3_free_handle(H)).

:- end_tests(floating_point).
