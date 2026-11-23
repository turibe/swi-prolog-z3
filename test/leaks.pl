%%% -*- Mode: Prolog; Module: leaks; -*-

%% Leak check for the C wrapper, run with `make leaks` (macOS only).
%%
%% Runs a workload that exercises most of z3_swi_foreign.c, including the error paths, then runs
%% macOS's `leaks` tool on this process. Fails if any leaked block was allocated with
%% z3_swi_foreign.so on its call stack, by the C code itself or by Z3 or the C library on its behalf.
%%
%% Blocks allocated by SWI-Prolog's PL_malloc_uncollectable are not counted, even when the call came
%% from z3_swi_foreign.so: SWI-Prolog uses it for permanent tables (functors, and the atom table, which
%% grows when the C code creates blobs) that `leaks` cannot see it still references. They are listed
%% in the summary. SWI-Prolog also leaves a few such blocks from startup.
%%
%% Needs MallocStackLogging=1 in the environment when swipl starts, so leaks can show call stacks;
%% the make target sets it. Usage: MallocStackLogging=1 swipl -q test/leaks.pl [Iterations]

:- module(leaks, []).

:- use_module('../z3_swi_foreign').
:- use_module(library(readutil)).
:- use_module(library(lists)).

:- initialization(main, main).

main(Argv) :-
    (   member(A, Argv), atom_number(A, N) -> true ; N = 100 ),   % see LEAK_ITERATIONS in the Makefile
    (   getenv('MallocStackLogging', _)
    ->  true
    ;   format(user_error, "MallocStackLogging is not set; leaks cannot show call stacks.~n", []),
        halt(2)
    ),
    format("Running leak workload, ~D iterations...~n", [N]),
    workload(N),
    % If the last iteration dropped a handle, a stale reference on Prolog's stacks can keep atom
    % garbage collection from reclaiming it; one more explicitly freed handle clears that.
    z3_new_handle(Flush), z3_free_handle(Flush),
    garbage_collect,
    garbage_collect_atoms,
    % Every handle is now freed or collected, so Z3's global memory can be freed too. This also
    % checks that z3_finalize_memory/0 succeeds when no handle is alive.
    catch(z3_swi_foreign:z3_finalize_memory, E,
          ( print_message(error, E),
            format(user_error, "z3_finalize_memory refused: some handle is still alive.~n", []),
            halt(2) )),
    run_leaks(Report),
    check_report(Report).

main :- current_prolog_flag(argv, Argv), main(Argv).

% ---------------------------------------------------------------------------- workload

workload(N) :-
    forall(between(1, N, I),
           (   iteration(I)
           ->  true
           ;   format("FAIL: workload iteration ~w failed (a goal in iteration/1 no longer succeeds)~n", [I]),
               halt(2)
           )).

% One iteration with its own handle, so everything a handle owns is created and freed each time.
iteration(I) :-
    z3_new_handle(H),
    z3_declare_enum(H, color, [red, green, blue]),
    z3_declare_function(H, f(int), int),
    z3_assert(H, a:int > I),
    z3_assert(H, f(a) = (b:int) + 1),
    z3_assert(H, c:color <> red),
    z3_assert(H, bv:bv(8) = int2bv(8, 5)),
    z3_assert(H, (r:real) * (r:real) = 2.0),       % an irrational value in the model
    z3_assert(H, (sqrt2:real) = algebraic(0.0, root([-2, 0, 1], 1))),   % and one given to Z3
    z3_assert(H, (str:string) = str_concat("héllo ", int_to_str(str_len("✓")))),
    z3_assert(H, str_contains(str:string, "1")),
    z3_assert(H, select(store(arr:array(int, array(int, real)), I, const_array(int, 1.5)), I) = select(arr:array(int, array(int, real)), 0)),
    z3_solver_push(H, _),
    z3_assert(H, between(d:int, 1, 3)),
    z3_assert(H, d:int <> e:real),
    z3_set_timeout(H, 60000),
    z3_interrupt(H),                          % no check running: no effect
    z3_check(H, l_true),
    z3_reason_unknown(H, _),
    z3_assert(H, implies(t1:bool, (core_x:int) < 0)),
    z3_check_assumptions(H, [t1], _),
    z3_get_unsat_core(H, _),
    optimization(I),
    quantifiers,
    floating_point,
    smtlib2,
    datatypes,
    z3_model_lists(H, _),
    z3_model_assocs(H, _),
    z3_get_model(H, M),
    z3_model_eval(H, M, a + 1, true, _),
    z3_free_model(H, M),
    z3_get_model(H, _Unfreed),              % left for garbage collection
    z3_solver_pop(H, 1, _),
    z3_simplify(H, a * 3 + a, _),
    z3_solver_assertions(H, _),
    z3_declarations(H, _),
    z3_enum_declarations(H, _),
    z3_swi_foreign:term_to_z3_ast(H, 1r3 + (x:real), Ast),
    z3_swi_foreign:z3_ast_to_term(H, Ast, _),
    error_paths(H),
    z3_reset_declarations(H),
    z3_free_handle(H),
    (   I mod 10 =:= 0 -> z3_new_handle(_Dropped) ; true ).   % left for garbage collection

% Optimization, on a handle of its own: on the handle above, which has nonlinear and string
% constraints, the optimizer can take until the timeout.
optimization(I) :-
    z3_new_handle(H),
    z3_assert(H, (u:int) >= 0),
    z3_assert(H, (u:int) + (v:int) =< I),
    z3_optimize(H, [maximize(u + 2*v), soft((v:int) > 3, 2), minimize(u)], _, _, M),
    ( M == none -> true ; z3_model_lists(H, M, _), z3_free_model(H, M) ),
    z3_optimize(H, [soft(w:bool)], _, _, _),               % model left for garbage collection
    catch(z3_optimize(H, [foo], _, _, _), _, true),         % a bad objective, after the optimizer exists
    z3_free_handle(H).

% Quantifiers, on a handle of their own, for the same reason as optimization; reading the assertions
% back converts quantifiers and their bound variables to Prolog.
quantifiers :-
    z3_new_handle(H),
    z3_set_timeout(H, 2000),
    z3_declare_function(H, qf(int), int),
    z3_assert(H, forall([qx:int], exists([qy:int], qy > qx))),
    z3_assert(H, forall([qx:int, qz:real], qf(qx) * 0 = 0 or qz > 0.0)),
    z3_check(H, _),
    z3_solver_assertions(H, _),
    \+ z3_assert(H, forall([qx], qx > 0)),                  % malformed: no sort
    z3_free_handle(H).

% Floating point: sorts, values (special ones, and float128's exact rationals), conversions, and
% converting models and assertions back, including formulas that fail part-way through.
floating_point :-
    z3_new_handle(H),
    forall(member(N:S, [fx:float32, fd:float64, fq:float128, fm:roundingmode, fb:bv(32)]),
           z3_declare_function(H, N, S)),
    z3_assert(H, fp_lt(fp_add(fm, fx, fp_value(0.1, float32)), fp_value(inf, float32))),
    z3_assert(H, fq = fp_div(rne, fp_value(1, float128), fp_value(3, float128))),
    z3_assert(H, fb = fp_to_sbv(rtz, to_fp(rne, fd, float32), 32)),
    z3_assert(H, not(fp_is_nan(fd)) and fp_eq(fp_from_ieee_bv(fb, float32), fx)),
    z3_check(H, _),
    z3_model_lists(H, _),
    z3_solver_assertions(H, _),
    \+ z3_assert(H, fp_add(rne, fx, fd) = fx),                % different formats
    \+ z3_assert(H, fp_value(foo, float32) = fx),             % not a value
    z3_free_handle(H).

% SMT-LIB2: exporting, parsing (with the handle's declarations and enums, typed numerals and a
% floating-point literal), and running a script; and a parse error and a redeclaration.
smtlib2 :-
    z3_new_handle(H),
    z3_declare_enum(H, scolor, [sred, sgreen]),
    forall(member(N:S, [sx:int, sr:real, sw:bv(8), sq:float32, sc:scolor]), z3_declare_function(H, N, S)),
    z3_assert(H, sx > 2 and sr = 1.5 and sw = int2bv(8, 7) and sq = fp_value(0.5, float32) and sc = sred),
    z3_solver_smtlib2(H, String),
    z3_parse_smtlib2(H, "(declare-const sy Int) (assert (> sy sx)) (assert (= sc sgreen))", _, _),
    z3_free_handle(H),
    z3_new_handle(H2),
    z3_parse_smtlib2(H2, String, Fs, _),
    forall(member(F, Fs), z3_assert(H2, F)),
    z3_solver_assertions(H2, _),
    \+ z3_parse_smtlib2(H2, "(assert (> z", _, _),
    \+ z3_parse_smtlib2(H2, "(declare-const sx Real) (assert (> sx 1.0))", _, _),
    z3_free_handle(H2),
    z3_eval_smtlib2("(declare-const a Int) (assert (> a 5)) (check-sat) (get-model)", _),
    \+ z3_eval_smtlib2("(assert (> undeclared 5))", _).

% Datatypes: declaring (mutually recursive, and a record), listing them and their functions, models
% and assertions with constructors and recognizers; and declarations that raise errors or fail.
datatypes :-
    z3_new_handle(H),
    z3_declare_datatypes(H, [dlist-[dnil, dcons(dhead:int, dtail:dlist)]]),
    z3_declare_datatypes(H, [dexpr-[dnum(dval:int), dblock(dbody:dstmt)], dstmt-[dskip, deval(de:dexpr)]]),
    z3_declare_datatypes(H, [dpoint-[dpoint(dx:real, dy:real)]]),
    z3_datatypes(H, _),
    z3_datatype_declarations(H, _),
    z3_declare_function(H, dl, dlist),
    z3_assert(H, is_dcons(dl) and dhead(dl) > 2 and is_dnil(dtail(dl))),
    z3_check(H, _),
    z3_model_lists(H, _),
    z3_solver_assertions(H, _),
    z3_solver_smtlib2(H, _),
    catch(z3_declare_datatypes(H, [dlist-[dfoo]]), _, true),
    catch(z3_declare_datatypes(H, [dbad-[dc(1)]]), _, true),
    catch(z3_declare_datatypes(H, [drose-[drn(dk:array(int, drose))]]), _, true),
    \+ z3_declare_datatypes(H, [dstream-[dscons(dsh:int, dst:dstream)]]),
    z3_free_handle(H).

% Formulas and arguments that fail or raise errors part-way through conversion.
error_paths(H) :-
    forall(bad_formula(F), ignore(z3_swi_foreign:term_to_z3_ast(H, F, _))),
    ignore(catch(z3_declare_enum(H, bad, [a|_]), _, true)),
    ignore(catch(z3_assert(H, _ > 1), _, true)),
    ignore(z3_remove_declaration(H, nosuch, 0)),
    ignore(catch(z3_solver_pop(H, -1, _), _, true)),
    ignore(catch(z3_solver_pop(H, 99, _), _, true)).

bad_formula(between(x, 1)).                          % wrong arity
bad_formula(undeclared_fn(x)).                       % missing declaration
bad_formula(x:foo = y:bar).                          % sort mismatch
bad_formula(bv_numeral([1, foo])).                   % bad bit
bad_formula(bv2int(undeclared_fn(x), true)).         % bad subterm in a special case
bad_formula(mk_unsigned_int64(-1, int)).             % out of range
bad_formula(atleast(p:bool, q:bool, notanint)).      % bad bound
bad_formula(algebraic(0.0, root([-2, 0, 1], 3))).     % no such root
bad_formula(str_len(3) = 1).                          % not a string

% ---------------------------------------------------------------------------- leaks report

run_leaks(Report) :-
    current_prolog_flag(pid, Pid),
    tmp_file_stream(text, File, S), close(S),
    format(atom(Cmd), "leaks ~w > '~w' 2>/dev/null", [Pid, File]),
    shell(Cmd, _),                          % leaks exits 1 whenever it finds any leak
    read_file_to_string(File, Report, []),
    (   sub_string(Report, _, _, _, "leaks for")
    ->  true
    ;   format(user_error, "leaks did not produce a report; see ~w~n", [File]),
        halt(2)
    ),
    nb_setval(leaks_report_file, File).

check_report(Report) :-
    split_string(Report, "\n", "", Lines),
    forall(( member(L, Lines), sub_string(L, _, _, _, "leaks for") ), format("~s~n", [L])),
    stack_sections(Lines, Sections),
    partition(swi_table_section, Sections, SwiTables, Others),
    include(project_section, Others, Ours),
    length(Sections, NS),
    length(SwiTables, NT),
    length(Ours, NO),
    nb_getval(leaks_report_file, File),
    format("~d leak stacks: ~d are SWI-Prolog tables (PL_malloc_uncollectable), not counted.~n", [NS, NT]),
    (   Ours == []
    ->  format("OK: none of the other ~d leak stacks involve z3_swi_foreign.so.~n", [NS - NT])
    ;   format("FAIL: ~d of ~d leak stacks involve z3_swi_foreign.so:~n~n", [NO, NS]),
        forall(member(Sec, Ours), (atomic_list_concat(Sec, '\n', Text), format("~w~n~n", [Text]))),
        format("Full report: ~w~n", [File]),
        halt(1)
    ).

% A section starts at a "STACK OF ..." line and runs to the next blank line.
stack_sections([], []).
stack_sections([L|Ls], Sections) :-
    (   sub_string(L, 0, _, _, "STACK OF")
    ->  take_section(Ls, Body, Rest),
        Sections = [[L|Body]|More],
        stack_sections(Rest, More)
    ;   stack_sections(Ls, Sections)
    ).

take_section([], [], []).
take_section([L|Ls], Body, Rest) :-
    (   normalize_space(string(""), L)
    ->  Body = [], Rest = Ls
    ;   Body = [L|Body1], take_section(Ls, Body1, Rest)
    ).

% The section header names the allocating function, as in
% "STACK OF 2 INSTANCES OF 'ROOT LEAK: <malloc in PL_malloc_uncollectable>':".
swi_table_section([Header|_]) :-
    sub_string(Header, _, _, _, " in PL_malloc_uncollectable>").

% A stack frame line looks like "3   z3_swi_foreign.so   0x100e98d0c term_to_ast + 524".
project_section(Section) :-
    member(Line, Section),
    split_string(Line, " \t", " \t", Words0),
    exclude(==(""), Words0, [Frame, Image|_]),
    number_string(_, Frame),
    Image == "z3_swi_foreign.so",
    !.
