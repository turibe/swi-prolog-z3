#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: explanation_examples; -*-

%% Examples of explaining and relaxing inconsistent constraints, with the high-level z3.pl API:
%%
%%   z3_explain(Formulas, Core)    Core is a minimal subset of Formulas that conflict: what to change.
%%   z3_relax(Formulas, Kept)      Kept is a maximal subset of Formulas that can all hold, preferring
%%                                 earlier formulas: what can still be done.
%%   z3_unsat_core(Formulas, Core) Like z3_explain, faster, but Core need not be minimal.
%%   z3_optimize(Objectives, M)    With soft(F, Weight) objectives: the best choice by weight.
%%
%% All of them work relative to the formulas pushed so far, and leave the solver as it was.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/explanations.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/explanations).
%%     ?- example(meeting_conflict).
%%     ?- run_tests(explanation_examples).

:- module(explanation_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').
:- use_module('../quickexplain').

:- discontiguous question/2, answer/2.   % kept next to each example's data
:- op(740, xfy, <>).                     % as in z3.pl, so answers print as they are written

% Run main only when this file is the script swipl was started with, not when it is loaded.
:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

%! example(?Name, -Answer) is nondet.
%  Answer is the result of the example Name, computed from a fresh solver.
example(Name, Answer) :-
    question(Name, _),
    z3_reset,
    answer(Name, Answer).

%! example(?Name) is nondet.
%  Runs the example Name, printing its question and answer.
example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(explanation_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

% ------------------------------------------------------------------------------------------------
% Scheduling a meeting. Each request has a name, so the answers can say whose requests they are.
% The meeting starts at hour h.

meeting_requests([ office_hours - (h:int >= 9 and h =< 17),
                   alice        - (h >= 13),             % Alice is busy in the mornings
                   bob          - (h < 12),              % Bob only has mornings
                   carol        - (h <> 15),             % Carol has another meeting at 15:00
                   lunch        - (h <> 12) ]).          % nobody wants to meet at noon

% The names of the requests whose formulas are Formulas.
names(Requests, Formulas, Names) :-
    findall(Name, (member(F, Formulas), member(Name-G, Requests), G == F), Names).

question(meeting_conflict,
         "The meeting requests cannot all be met. Which ones conflict?").
question(meeting_relaxed,
         "Listing the requests from most to least important, which can be kept, and when can we meet?").

answer(meeting_conflict, Conflicting) :-
    meeting_requests(Requests),
    pairs_values(Requests, Formulas),
    z3_explain(Formulas, Core),
    names(Requests, Core, Conflicting).

% z3_relax/2 prefers earlier formulas, so the list order is the priority order. A model of the kept
% requests gives a time.
answer(meeting_relaxed, kept(Kept)-at(H)) :-
    meeting_requests(Requests),
    pairs_values(Requests, Formulas),
    z3_relax(Formulas, KeptFormulas),
    names(Requests, KeptFormulas, Kept),
    maplist(z3_push, KeptFormulas),
    z3_model(M),
    memberchk(h = H, M.constants).

% ------------------------------------------------------------------------------------------------
% Configuring a car. Facts, which must hold, are pushed first; wishes are what can be given up.
% Booleans count as 0 or 1 in arithmetic, so the price adds the cost of each option chosen.

car_facts :-
    z3_push(price:int = 25000 + 1500 * sunroof:bool + 2500 * leather:bool + 3000 * sport:bool),
    z3_push(implies(sport, leather)).                    % the sport package needs leather seats

car_wishes([ budget  - (price =< 30000),
             sport   - sport,
             sunroof - sunroof,
             leather - leather ]).

question(car_conflict,
         "A sport package, sunroof and leather seats, within a budget of 30000: which wishes conflict?").
question(car_relaxed,
         "Keeping the budget first, then the wishes in order, what can we have, and at what price?").
question(car_weighted,
         "Within the budget, with the sport package worth 5, the sunroof 2 and leather 1, what is best?").

% The facts say the sport package needs leather, so the sport package alone already breaks the
% budget (25000 + 3000 + 2500 = 30500): budget and sport conflict, without the other wishes.
answer(car_conflict, Conflicting) :-
    car_facts,
    car_wishes(Wishes),
    pairs_values(Wishes, Formulas),
    z3_explain(Formulas, Core),
    names(Wishes, Core, Conflicting).

% The sport package needs leather, so with it the price is 30500: over budget. So it goes.
answer(car_relaxed, kept(Kept)-price(Price)) :-
    car_facts,
    car_wishes(Wishes),
    pairs_values(Wishes, Formulas),
    z3_relax(Formulas, KeptFormulas),
    names(Wishes, KeptFormulas, Kept),
    maplist(z3_push, KeptFormulas),
    z3_model(M),
    memberchk(price = Price, M.constants).

% With weights, z3_optimize/2's soft constraints find the best choice by total weight. The sport
% package weighs the most, but cannot fit the budget, so the answer is the same.
answer(car_weighted, options(Options)-price(Price)) :-
    car_facts,
    z3_push(price =< 30000),
    z3_optimize([soft(sport, 5), soft(sunroof, 2), soft(leather, 1)], M),
    findall(O, (member(O, [sport, sunroof, leather]), memberchk(O = true, M.constants)), Options),
    memberchk(price = Price, M.constants).

% ------------------------------------------------------------------------------------------------
% A quick first answer. z3_unsat_core/2 asks Z3 once, so it is fast, even on large problems. Its core
% need not be minimal: it may include formulas that the conflict does not need. For small problems
% like this one it usually is minimal already; z3_explain/2 on the core checks, and trims it if not.
% (z3_minimal_core/2 does both steps.)

question(meeting_unsat_core,
         "Which requests does a quick unsat core blame, and does z3_explain trim any of them?").

answer(meeting_unsat_core, core(CoreNames)-minimal(MinimalNames)) :-
    meeting_requests(Requests),
    pairs_values(Requests, Formulas),
    z3_unsat_core(Formulas, Core),
    names(Requests, Core, CoreNames),
    z3_explain(Core, Minimal),
    names(Requests, Minimal, MinimalNames).

% ------------------------------------------------------------------------------------------------
% Why z3_explain/2 rather than QuickXplain with z3_push. These four formulas conflict, and all four
% are needed: f(a) = f(b), with a = 1 and b = 2, says f(1) = f(2).

question(why_z3_explain,
         "Which of f(a) = f(b), a = 1, b = 2 and f(1) <> f(2) conflict, with qexplain(z3_push, ...) and with z3_explain?").

% qexplain/3 pushes formulas one at a time. Pushed alone, f(a) = f(b) gives a, b and f no numeric
% type, so a = 1 is then a type error, which z3_push reports by failing, as it does for a conflict;
% so QuickXplain wrongly blames the first two. z3_explain/2 types all the formulas together first.
answer(why_z3_explain, [qexplain-WithQexplain, z3_explain-WithExplain]) :-
    Formulas = [f(a) = f(b), a = 1, b = 2, f(1) <> f(2)],
    qexplain(z3_push, Formulas, WithQexplain),
    z3_reset,
    z3_explain(Formulas, WithExplain).

% ------------------------------------------------------------------------------------------------

:- begin_tests(explanation_examples).

expected(meeting_conflict, [alice, bob]).
expected(meeting_relaxed, kept([office_hours, alice, carol, lunch])-at(_)).
expected(car_conflict, [budget, sport]).
expected(car_relaxed, kept([budget, sunroof, leather])-price(29000)).
expected(car_weighted, options([sunroof, leather])-price(29000)).
expected(meeting_unsat_core, core(_)-minimal([alice, bob])).
expected(why_z3_explain, [qexplain-[f(a) = f(b), a = 1], z3_explain-[f(a) = f(b), a = 1, b = 2, f(1) <> f(2)]]).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(subsumes_term(Expected, Answer)).

% The meeting time satisfies the kept requests.
test(meeting_time) :-
    example(meeting_relaxed, kept(_)-at(H)),
    assertion((H >= 13, H =< 17, H =\= 15, H =\= 12)).

% The unsat core contains the minimal one.
test(unsat_core_contains_minimal) :-
    example(meeting_unsat_core, core(Core)-minimal(Minimal)),
    assertion(subset(Minimal, Core)).

:- end_tests(explanation_examples).
