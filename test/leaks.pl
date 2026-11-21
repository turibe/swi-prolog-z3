%%% -*- Mode: Prolog; Module: leaks; -*-

%% Leak check for the C wrapper, run by `make leaks` (macOS only).
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
    (   member(A, Argv), atom_number(A, N) -> true ; N = 2000 ),
    (   getenv('MallocStackLogging', _)
    ->  true
    ;   format(user_error, "MallocStackLogging is not set; leaks cannot show call stacks.~n", []),
        halt(2)
    ),
    format("Running leak workload, ~D iterations...~n", [N]),
    workload(N),
    garbage_collect,
    garbage_collect_atoms,
    run_leaks(Report),
    check_report(Report).

main :- current_prolog_flag(argv, Argv), main(Argv).

% ---------------------------------------------------------------------------- workload

workload(N) :-
    forall(between(1, N, I), iteration(I)).

% One iteration with its own handle, so everything a handle owns is created and freed each time.
iteration(I) :-
    z3_new_handle(H),
    z3_declare_enum(H, color, [red, green, blue]),
    z3_declare_function(H, f(int), int),
    z3_assert(H, a:int > I),
    z3_assert(H, f(a) = (b:int) + 1),
    z3_assert(H, c:color <> red),
    z3_assert(H, bv:bv(8) = int2bv(8, 5)),
    z3_solver_push(H, _),
    z3_assert(H, between(d:int, 1, 3)),
    z3_assert(H, d:int <> e:real),
    z3_check(H, l_true),
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
