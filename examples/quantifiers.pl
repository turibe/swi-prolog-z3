#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: quantifier_examples; -*-

%% Examples of quantifiers, forall(Vars, Body) and exists(Vars, Body), with the high-level z3.pl API.
%%
%% Run it as a script, to print each question and Z3's answer:
%%     ./examples/quantifiers.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/quantifiers).
%%     ?- example(syllogism).
%%     ?- run_tests(quantifier_examples).
%%
%% A note on what to expect. Z3 is good at proving that something follows from quantified facts:
%% it looks for a contradiction, instantiating the quantifiers with the terms in the problem. It is
%% much weaker at showing that quantified facts are consistent, since that means finding a model
%% that works for every value, often infinitely many. So the examples ask "does A imply B?" in one
%% call, as z3_is_implied(implies(A, B)), rather than pushing A and then asking about B: pushing A
%% alone makes Z3 check A's consistency, which it may not be able to decide. A timeout keeps such
%% checks from running for too long; one example shows what happens then.

:- module(quantifier_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').

% Run main only when this file is the script swipl was started with, not when it is loaded.
:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

% Each check gets at most this many milliseconds (see the note above).
timeout_ms(1000).

%! example(?Name, -Answer) is nondet.
%  Answer is the result of the example Name, computed from a fresh solver.
example(Name, Answer) :-
    question(Name, _),
    timeout_ms(Ms),
    z3_set_timeout(Ms),
    z3_reset,
    answer(Name, Answer).

%! example(?Name) is nondet.
%  Runs the example Name, printing its question and answer.
example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~w~n~n", [Question, Answer]).

main :-
    forall(question(Name, _), example(Name)),
    z3_set_timeout(0).

% ------------------------------------------------------------------------------------------------
% The examples: a question, in words, and the code that answers it.

question(syllogism,
         "All men are mortal, and Socrates is a man. Is Socrates mortal?").
question(monotone,
         "If f is strictly increasing, is f(1) < f(3)?").
question(definition,
         "If double(x) = 2 * x for every x, what is double(21)?").
question(square_roots,
         "Is there an integer whose square is 2? And a real one?").
question(sorted_array,
         "If the array a is sorted from index 0 to 3, and a[0] = 10, is a[3] at least 10?").
question(induction,
         "If p(0) holds, and p(x) implies p(x + 1) for every x, does p(5) hold?").
question(explanation,
         "f(f(x)) = x for every x, f(0) = 1, g(3) = 4 and f(1) = 2 are inconsistent. Which of them conflict?").
question(fixed_point,
         "If f(f(x)) = x for every integer x, must f have a fixed point, an x with f(x) = x?").

% All men are mortal; Socrates is a man. The sort person is uninterpreted: nothing is known about
% it but what the formulas say.
answer(syllogism, Answer) :-
    z3_push(forall([x:person], implies(man(x), mortal(x)))),
    z3_push(man(socrates:person)),
    yes_no(z3_is_implied(mortal(socrates)), Answer).

% A property of a function, used for a conclusion: Z3 instantiates the axiom with x = 1, y = 3.
% (Asked as one implication; see the note at the top.)
answer(monotone, Answer) :-
    Increasing = forall([x, y], implies(x < y, f(x) < f(y))),
    yes_no(z3_is_implied(implies(Increasing, f(1) < f(3))), Answer).

% Defining a function by an axiom, then computing with it. This axiom is one Z3 handles directly,
% so it can be pushed, and a model gives the value.
answer(definition, double(21) = Value) :-
    z3_push(forall([x], double(x) = 2 * x)),
    z3_push(y = double(21)),
    z3_eval(y, Value).

% exists: no integer has square 2, but some real does.
answer(square_roots, [integer-Integer, real-Real]) :-
    yes_no(z3_is_consistent(exists([x:int], x * x = 2)), Integer),
    yes_no(z3_is_consistent(exists([x:real], x * x = 2.0)), Real).

% Quantifying over array indices: sortedness, stated once for all indices, gives a[3] >= a[0].
answer(sorted_array, Answer) :-
    Sorted = forall([i], implies(0 =< i and i < 3, select(a:array(int, int), i) =< select(a, i + 1))),
    yes_no(z3_is_implied(implies(Sorted and select(a, 0) = 10, select(a, 3) >= 10)), Answer).

% Like induction, but only up to 5: Z3 instantiates the rule with x = 0, 1, 2, 3, 4.
answer(induction, Answer) :-
    Step = forall([x:int], implies(p(x), p(x + 1))),
    yes_no(z3_is_implied(implies(Step and p(0), p(5))), Answer).

% Explaining an inconsistency: z3_unsat_core/2 picks out the formulas that conflict:
% f(f(0)) = f(1) = 2, not 0. g(3) = 4 has nothing to do with it.
% z3_minimal_core/2 would also guarantee that no smaller set conflicts, by checking that the subsets
% are consistent; with quantifiers, Z3 may not decide those checks, so each can take until the
% timeout (5 s here, against a few milliseconds). Here the unsat core happens to be minimal already.
answer(explanation, Conflicting) :-
    z3_unsat_core([forall([x], f(f(x)) = x), f(0) = 1, g(3) = 4, f(1) = 2], Conflicting).

% A question Z3 cannot settle: the answer is no (f(x) = 1 - x swaps 0 and 1, 2 and -1, and so on,
% and fixes nothing), but proving that means finding such an f, which Z3's search for models of
% quantified formulas does not manage. It reports unknown, and the timeout says why it stopped.
answer(fixed_point, Answer) :-
    Involution = forall([x:int], f(f(x)) = x),
    z3_push(not(implies(Involution, exists([x:int], f(x) = x))), Status),
    (   Status == l_undef
    ->  z3_reason_unknown(Reason),
        format(atom(Answer), "unknown (Z3 stopped: ~w)", [Reason])
    ;   Status == l_false
    ->  Answer = yes
    ;   Answer = no
    ).

yes_no(Goal, Answer) :- ( call(Goal) -> Answer = yes ; Answer = no ).

% ------------------------------------------------------------------------------------------------

:- begin_tests(quantifier_examples, [cleanup(z3_set_timeout(0))]).

expected(syllogism, yes).
expected(monotone, yes).
expected(definition, double(21) = 42).
expected(square_roots, [integer-no, real-yes]).
expected(sorted_array, yes).
expected(induction, yes).
expected(explanation, [forall([x], f(f(x)) = x), f(0) = 1, f(1) = 2]).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% This one depends on Z3 not finding a model; if a later Z3 does, the answer becomes no.
test(fixed_point_undecided) :-
    example(fixed_point, Answer),
    assertion(( sub_atom(Answer, 0, _, _, unknown) ; Answer == no )).

:- end_tests(quantifier_examples).
