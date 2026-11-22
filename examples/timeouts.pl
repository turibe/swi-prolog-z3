#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: timeout_examples; -*-

%% Examples of stopping a long check. Some problems take Z3 a long time, or forever; these are ways
%% to stop it:
%%
%%   z3_set_timeout(Ms)              each check gives up after Ms milliseconds, with status l_undef
%%   call_with_time_limit(S, Goal)   stops Goal, including a running check, raising time_limit_exceeded
%%   thread_signal/2, Ctrl-C         likewise, as for any Prolog goal
%%   z3_interrupt(Handle)            from another thread: the running check returns l_undef
%%   z3_reason_unknown(Reason)       why the last check had status l_undef
%%
%% The slow problem is the pigeonhole problem: 10 pigeons cannot fit in 9 holes, one per hole, but as
%% plain clauses it takes Z3 several seconds to prove it (see examples/pigeonhole.pl).
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/timeouts.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/timeouts).
%%     ?- example(timeout).
%%     ?- run_tests(timeout_examples).

:- module(timeout_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').
:- use_module('../z3_swi_foreign', [z3_new_handle/1, z3_free_handle/1, z3_check/2, z3_interrupt/1,
                                    z3_reason_unknown/2]).
:- use_module(pigeonhole, [pigeonhole/2, pigeon/3]).

:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

example(Name, Answer) :- question(Name, _), z3_reset, answer(Name, Answer), z3_set_timeout(0).

example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(timeout_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

% The pigeonhole problem with N + 1 pigeons and N holes, as one formula for z3_push.
pigeonhole_formula(N, F) :-
    N1 is N + 1,
    findall(C, pigeonhole_clause(N, N1, C), Cs),
    F =.. [and|Cs].
pigeonhole_clause(N, N1, C) :-
    between(1, N1, I), findall(P, (between(1, N, J), pigeon(I, J, P)), Ps), C =.. [or|Ps].
pigeonhole_clause(N, N1, not(and(A, B))) :-
    between(1, N, J), between(1, N1, I), between(1, N1, K), I < K, pigeon(I, J, A), pigeon(K, J, B).

% Runs Goal, giving how long it took, in tenths of a second.
timed(Goal, Seconds) :-
    get_time(T0), call(Goal), get_time(T1),
    Seconds is round((T1 - T0) * 10) / 10.

question(timeout,
         "With a 0.5 s timeout, what happens when we push the 10-pigeon problem?").
question(time_limit,
         "Without a timeout, can call_with_time_limit/2 stop the check after 0.5 s?").
question(interrupt,
         "Can another thread stop the check, with z3_interrupt/1?").
question(still_usable,
         "After a check is stopped, does the solver still work?").

% The check gives up: status l_undef, and the reason says why (timeout or canceled, depending on
% which part of Z3 stops).
answer(timeout, status(Status)-reason(Reason)-seconds(S)) :-
    z3_set_timeout(500),
    pigeonhole_formula(9, F),
    timed(z3_push(F, Status), S),
    z3_reason_unknown(Reason).

answer(time_limit, caught(E)-seconds(S)) :-
    pigeonhole_formula(9, F),
    timed(catch(call_with_time_limit(0.5, z3_push(F, _)), E, true), S).

% z3_interrupt/1 works on a handle, so this uses the lower-level API (z3_swi_foreign) directly:
% one thread checks, another interrupts after 0.3 s. The check returns l_undef.
answer(interrupt, status(Status)-reason(Reason)-seconds(S)) :-
    z3_new_handle(H),
    pigeonhole(H, 9),
    thread_create((sleep(0.3), z3_interrupt(H)), Interrupter),
    timed(z3_check(H, Status), S),
    thread_join(Interrupter, _),
    z3_reason_unknown(H, Reason),
    z3_free_handle(H).

answer(still_usable, Status) :-
    z3_set_timeout(200),
    pigeonhole_formula(9, F),
    z3_push(F, _),
    z3_set_timeout(0),
    z3_reset,
    z3_push(x:int > 3, Status).

:- begin_tests(timeout_examples).

test(timeout) :-
    example(timeout, status(Status)-reason(Reason)-seconds(S)),
    assertion(Status == l_undef),
    assertion(memberchk(Reason, [timeout, canceled])),
    assertion(S < 1.5).

test(time_limit) :-
    example(time_limit, caught(E)-seconds(S)),
    assertion(E == time_limit_exceeded),
    assertion(S < 1.5).

test(interrupt) :-
    example(interrupt, status(Status)-reason(Reason)-seconds(S)),
    assertion(Status == l_undef),
    assertion(Reason == interrupted),
    assertion(S < 1.5).

test(still_usable) :-
    example(still_usable, Status),
    assertion(Status == l_true).

:- end_tests(timeout_examples).
