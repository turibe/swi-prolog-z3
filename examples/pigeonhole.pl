#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: pigeonhole; -*-

%% The pigeonhole problem, as plain clauses for the low-level z3_swi_foreign API.
%%
%% Putting more pigeons than holes, one pigeon per hole, is impossible, but proving it with clauses
%% alone (no cardinality constraints) takes a SAT solver exponential time, so the problem gets slow
%% quickly: with N + 1 pigeons and N holes, N = 9 takes about a second. The test suite uses it to keep
%% a handle busy.
%%
%% Run it as a script, to time increasing sizes and show a solution for equal numbers:
%%     ./examples/pigeonhole.pl [MaxN]          (default MaxN = 9)
%% or load it, with z3_swi_foreign for the handle predicates, and call the predicates:
%%     ?- use_module(z3_swi_foreign), use_module(examples/pigeonhole).
%%     ?- z3_new_handle(H), pigeonhole(H, 4), z3_check(H, S).
%%     S = l_false.

:- module(pigeonhole, [
              pigeon/3,
              pigeonhole/2,
              pigeonhole/3
          ]).

:- use_module('../z3_swi_foreign').

% Run main only when this file is the script swipl was started with, not when it is loaded.
:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

%! pigeon(+I, +J, -P) is det.
%  P is the Boolean variable meaning "pigeon I is in hole J", as `p_I_J:bool`.
pigeon(I, J, P) :-
    format(atom(A), "p_~w_~w", [I, J]),
    P = (A:bool).

%! pigeonhole(+H, +N) is det.
%  Asserts on handle H the problem of putting N + 1 pigeons into N holes. Always unsatisfiable.
pigeonhole(H, N) :-
    N1 is N + 1,
    pigeonhole(H, N1, N).

%! pigeonhole(+H, +Pigeons, +Holes) is det.
%  Asserts on handle H that each of Pigeons pigeons is in one of Holes holes, and that no hole
%  holds two pigeons. Satisfiable exactly when Pigeons =< Holes.
pigeonhole(H, Pigeons, Holes) :-
    forall(between(1, Pigeons, I),                         % every pigeon is in some hole
           ( findall(P, (between(1, Holes, J), pigeon(I, J, P)), Ps),
             Or =.. [or|Ps],
             z3_assert(H, Or) )),
    forall(( between(1, Holes, J),                         % no hole holds two pigeons
             between(1, Pigeons, I), between(1, Pigeons, K), I < K ),
           ( pigeon(I, J, A), pigeon(K, J, B),
             z3_assert(H, not(and(A, B))) )).

main(Argv) :-
    (   member(A, Argv), atom_number(A, MaxN) -> true ; MaxN = 9 ),
    format("N + 1 pigeons, N holes (unsatisfiable):~n"),
    forall(between(1, MaxN, N), time_size(N)),
    format("~n4 pigeons, 4 holes (satisfiable), pigeon-hole pairs that are true in a model:~n"),
    setup_call_cleanup(z3_new_handle(H),
                       ( pigeonhole(H, 4, 4),
                         z3_check(H, l_true),
                         z3_model_lists(H, Model),
                         forall(member(Var = true, Model.constants), format("  ~w~n", [Var])) ),
                       z3_free_handle(H)).

main :- current_prolog_flag(argv, Argv), main(Argv).

time_size(N) :-
    setup_call_cleanup(z3_new_handle(H),
                       ( pigeonhole(H, N),
                         get_time(T0), z3_check(H, Status), get_time(T1) ),
                       z3_free_handle(H)),
    D is T1 - T0,
    format("  N = ~w: ~w in ~3f s~n", [N, Status, D]).
