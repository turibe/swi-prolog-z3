#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: knights_knaves; -*-

%% Knights and knaves, the logic puzzles of Raymond Smullyan. On the island, every inhabitant is a
%% knight, who always tells the truth, or a knave, who always lies. From what they say, work out
%% who is which.
%%
%% Each person is a Boolean constant, true for a knight. When A says S, then A is a knight exactly
%% when S is true: the formula a <=> S. A puzzle pushes one such formula for each statement, and a
%% person's kind is settled when Z3 can prove it: z3_is_implied(a) for a knight, z3_is_implied(not(a))
%% for a knave. When neither is implied, both are possible.
%%
%% Statements are written with knight(P) and knave(P), and, or, not, implies and <=>, and
%% knights(N, People), "exactly N of People are knights". For example:
%%     says(a, knave(a) and knave(b))       A says: "We are both knaves."
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/knights_knaves.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/knights_knaves).
%%     ?- example(both_knaves).
%%     ?- run_tests(knights_knaves).
%% or solve a puzzle of your own:
%%     ?- solve([a, b], [says(a, knight(b)), says(b, knave(a) or knave(b))], Kinds).

:- module(knights_knaves, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2,          % example(?Name, -Answer): Answer is the example's result
              solve/3             % solve(+People, +Statements, -Kinds): who is which
          ]).

:- use_module('../z3').

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
    format("~w~n  ~q~n~n", [Question, Answer]).

main :- forall(question(Name, _), example(Name)).

% ------------------------------------------------------------------------------------------------
% From statements to formulas, and from the solver to an answer.

%! statement_formula(+Statement, -Formula) is det.
%  Formula holds when Statement, says(Person, Claim), is made by someone of the right kind: a knight
%  making a true claim, or a knave making a false one.
statement_formula(says(P, Claim), P:bool <=> F) :- claim_formula(Claim, F).

claim_formula(knight(P), P:bool) :- !.
claim_formula(knave(P), not(P:bool)) :- !.
claim_formula(knights(N, People), Atleast and Atmost) :- !,
    % atleast and atmost take the Booleans, then the bound, as arguments.
    findall(P:bool, member(P, People), Typed),
    append(Typed, [N], Args),
    Atleast =.. [atleast | Args],
    Atmost =.. [atmost | Args].
claim_formula(not(A), not(FA)) :- !, claim_formula(A, FA).
claim_formula(Claim, F) :-
    Claim =.. [Op, A, B],
    memberchk(Op, [and, or, implies, <=>]), !,
    claim_formula(A, FA),
    claim_formula(B, FB),
    F =.. [Op, FA, FB].

%! solve(+People, +Statements, -Kinds) is det.
%  Kinds lists Person-Kind for each of People, with Kind knight, knave, or either when the statements
%  allow both. Kinds is impossible when no assignment of kinds fits the statements.
solve(People, Statements, Kinds) :-
    maplist(statement_formula, Statements, Formulas),
    (   maplist(z3_push, Formulas)
    ->  maplist(kind, People, Kinds)
    ;   Kinds = impossible
    ).

kind(P, P-Kind) :-
    (   z3_is_implied(P:bool)
    ->  Kind = knight
    ;   z3_is_implied(not(P:bool))
    ->  Kind = knave
    ;   Kind = either
    ).

% ------------------------------------------------------------------------------------------------
% The puzzles: who is on the island, and what they say.

% A says: "We are both knaves."
puzzle(both_knaves, [a, b], [says(a, knave(a) and knave(b))]).

% A says: "At least one of us is a knave."
puzzle(at_least_one, [a, b], [says(a, knave(a) or knave(b))]).

% A says: "We are the same kind." B says: "We are of different kinds."
puzzle(same_kind, [a, b], [says(a, knight(a) <=> knight(b)),
                           says(b, not(knight(a) <=> knight(b)))]).

% A says: "All of us are knaves." B says: "Exactly one of us is a knight."
puzzle(three, [a, b, c], [says(a, knave(a) and knave(b) and knave(c)),
                          says(b, knights(1, [a, b, c]))]).

% A says: "I am a knight."
puzzle(self_praise, [a], [says(a, knight(a))]).

% A says: "I am a knave."
puzzle(liar, [a], [says(a, knave(a))]).

% A says: "B is a knight." B says: "A is a knave." C says: "A is a knight." D says: "C and I are of
% different kinds."
puzzle(paradox, [a, b, c, d], [says(a, knight(b)),
                               says(b, knave(a)),
                               says(c, knight(a)),
                               says(d, not(knight(c) <=> knight(d)))]).

% ------------------------------------------------------------------------------------------------
% The examples: a question, in words, and the code that answers it.

question(both_knaves,
         "A says: \"We are both knaves.\" Who is which?").
question(at_least_one,
         "A says: \"At least one of us is a knave.\" Who is which?").
question(same_kind,
         "A says: \"We are the same kind.\" B says: \"We are of different kinds.\" Who is which?").
question(three,
         "A says: \"All of us are knaves.\" B says: \"Exactly one of us is a knight.\" Who is which?").
question(self_praise,
         "A says: \"I am a knight.\" Is A a knight?").
question(liar,
         "A says: \"I am a knave.\" Is A a knight?").
question(paradox,
         "A says: \"B is a knight.\" B: \"A is a knave.\" C: \"A is a knight.\" D: \"C and I are different.\" Nobody can say all that. Which statements conflict?").
question(road,
         "One road leads to the city. The guard at the fork is a knight or a knave. Ask: \"If I asked you whether the left road leads to the city, would you say yes?\" Does a yes mean it does?").

answer(Name, Kinds) :-
    puzzle(Name, People, Statements),
    Name \== paradox,
    solve(People, Statements, Kinds).

% A is a knight exactly when B is, and B exactly when A is not: no assignment works. z3_explain/2
% finds a smallest set of statements that cannot all be made, and the answer gives them as said.
% C and D are not to blame, whatever they are.
answer(paradox, Conflicting) :-
    puzzle(paradox, _, Statements),
    maplist(statement_formula, Statements, Formulas),
    z3_explain(Formulas, Core),
    findall(S, ( member(F, Core), nth1(I, Formulas, G), G == F, nth1(I, Statements, S) ), Conflicting).

% Someone asked a yes-or-no question Q answers yes exactly when they are a knight and Q is true, or a
% knave and Q is false: when guard <=> Q. The question asked here is about that answer, so the guard
% says yes when guard <=> (guard <=> left). The two lies of a knave cancel out, and the answer is
% yes exactly when left is true, for either kind of guard.
answer(road, Answer) :-
    Yes = (guard:bool <=> (guard <=> left:bool)),
    (   z3_is_implied(Yes <=> left) -> Answer = yes ; Answer = no ).

% ------------------------------------------------------------------------------------------------

:- begin_tests(knights_knaves).

expected(both_knaves, [a-knave, b-knight]).
expected(at_least_one, [a-knight, b-knave]).
expected(same_kind, [a-knave, b-knight]).
expected(three, [a-knave, b-knight, c-knave]).
expected(self_praise, [a-either]).
expected(liar, impossible).
expected(paradox, [says(a, knight(b)), says(b, knave(a))]).
expected(road, yes).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% Asking the guard directly does not work: a knave's yes means no.
test(direct_question_fails) :-
    z3_reset,
    \+ z3_is_implied((guard:bool <=> left:bool) <=> left).

:- end_tests(knights_knaves).
