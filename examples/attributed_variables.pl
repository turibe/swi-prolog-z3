#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: attributed_variable_examples; -*-

%% Examples of Prolog variables in Z3 formulas. A variable in a pushed formula stands for a Z3
%% constant (its attribute). Binding the variable, by any Prolog means, pushes that it equals its
%% value, and fails if that is inconsistent. This works both ways:
%%
%%   - Prolog generates values (member/2, between/3, permutation/2, ...), and Z3 prunes them as soon as
%%     they are bound, as a CLP solver does; and
%%   - Z3 finds values, and z3_label/1 binds the variables to them, one solution per answer.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/attributed_variables.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/attributed_variables).
%%     ?- example(send_more_money).
%%     ?- run_tests(attributed_variable_examples).

:- module(attributed_variable_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').

:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

example(Name, Answer) :- question(Name, _), z3_reset, answer(Name, Answer).

example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(attributed_variable_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

question(send_more_money,
         "SEND + MORE = MONEY, each letter a different digit: Prolog chooses digits with between/3, and Z3 rejects a choice as soon as it cannot lead to a solution.").
question(map_coloring,
         "Color the map of Australia in red, green and blue, choosing colors with member/2, so that neighbors differ. How many ways are there, and what is one?").
question(words,
         "Which of hello, world, yellow and bell contain \"ell\"? Prolog turns the atoms into strings; Z3 checks them.").
question(floats,
         "Which of 1.0, 1.0e7, 1.0e8 and 3.0e38, as float32 numbers, satisfy x + 1 == x?").
question(label_pairs,
         "Which positive integers x and y have x + y = 5? Z3 finds them, and z3_label/1 binds them, one pair per answer.").
question(label_square_root,
         "What does z3_label/1 bind q to, for q * q = 2 and q > 0?").
question(label_colorings,
         "With an enumeration sort of colors, can Z3 find the map colorings itself, without member/2?").
question(schedule,
         "Three 2-hour meetings, a, b and c, between 9 and 17, one after another: a not before 10, c starting before 13. Prolog tries each order with permutation/2; Z3 finds start times. Which orders work?").
question(explain,
         "Of X > 10, Y < 3, X < 5 and Y > 0, which conflict? The answer is the caller's own terms, with their variables.").

% Each between/3 binding pushes Letter == Digit and checks: a branch that cannot lead to a solution
% is cut at once, so far fewer than the 10^8 assignments are tried.
answer(send_more_money, solution(Digits)) :-
    Digits = [S, E, N, D, M, O, R, Y],
    maplist([V]>>z3_push(V:int >= 0 and V =< 9), Digits),
    z3_push(S > 0 and M > 0),
    z3_push(distinct(S, E, N, D, M, O, R, Y)),
    z3_push(1000*S + 100*E + 10*N + D + 1000*M + 100*O + 10*R + E
            = 10000*M + 1000*O + 100*N + 10*E + Y),
    maplist([V]>>between(0, 9, V), Digits), !.

% The colors are atoms, which Z3 takes as constants of an uninterpreted sort; bound ones are distinct
% here because neighbors are required to differ.
answer(map_coloring, ways(N)-first(First)) :-
    findall(Regions, australia_coloring(Regions), All),
    length(All, N),
    All = [First|_].

answer(words, Words) :-
    findall(W, ( z3_push(str_contains(S, "ell")),
                 member(W, [hello, world, yellow, bell]),
                 atom_string(W, S) ),
            Words).

answer(floats, Values) :-
    findall(V, ( z3_push(fp_eq(fp_add(rne, X:float32, fp_value(1, float32)), X)),
                 member(V, [1.0, 1.0e7, 1.0e8, 3.0e38]),
                 X = fp_value(V, float32) ),
            Values).

answer(label_pairs, Pairs) :-
    findall(X-Y, ( z3_push(X:int > 0 and Y:int > 0 and X + Y = 5), z3_label([X, Y]) ), Pairs0),
    msort(Pairs0, Pairs).

answer(label_square_root, Q) :-
    z3_push(Q:real * Q = 2.0 and Q > 0.0),
    once(z3_label([Q])).

% z3_declare_enum/2 makes the colors values of a sort, all different, so Z3 can choose them.
answer(label_colorings, ways(N)) :-
    z3_declare_enum(color, [red, green, blue]),
    findall(Regions, ( australia(Regions, Neighbors),
                       maplist([R]>>z3_push(R:color = R), Regions),
                       z3_push(Neighbors),
                       z3_label(Regions) ),
            All),
    length(All, N).

answer(schedule, Schedules) :-
    findall(Order-Starts, ( permutation([a, b, c], Order), schedule(Order, Starts) ), Schedules).

answer(explain, Core) :-
    z3_explain([X > 10, Y < 3, X < 5, Y > 0], Core).

% The regions of Australia, as variables, and the formula that neighbors differ.
australia([WA, NT, SA, Q, NSW, V], and(WA <> NT, WA <> SA, NT <> SA, NT <> Q, SA <> Q, SA <> NSW, SA <> V,
                                       Q <> NSW, NSW <> V)).

australia_coloring(Regions) :-
    australia(Regions, Neighbors),
    z3_push(Neighbors),
    maplist([R]>>member(R, [red, green, blue]), Regions).

% Starts are the start times of the meetings in Order, if they can be scheduled in that order.
schedule(Order, Starts) :-
    pairs_keys_values(Meetings, Order, Starts),
    maplist([_-S]>>z3_push(S:int >= 9 and S + 2 =< 17), Meetings),
    one_after_another(Starts),
    memberchk(a-A, Meetings), z3_push(A >= 10),
    memberchk(c-C, Meetings), z3_push(C < 13),
    z3_label(Starts), !.

one_after_another([_]) :- !.
one_after_another([S1, S2|Ss]) :- z3_push(S2 >= S1 + 2), one_after_another([S2|Ss]).

:- begin_tests(attributed_variable_examples).

test(send_more_money) :-
    example(send_more_money, solution(Digits)),
    assertion(Digits == [9, 5, 6, 7, 1, 0, 8, 2]).

% The 3 colors of the central region SA, then 2 ways to alternate around it.
test(map_coloring) :-
    example(map_coloring, ways(N)-first([WA, NT, SA, Q, NSW, V])),
    assertion(N == 6),
    assertion((WA \== NT, WA \== SA, NT \== SA, NT \== Q, SA \== Q, SA \== NSW, SA \== V, Q \== NSW, NSW \== V)).

test(words) :-
    example(words, Words),
    assertion(Words == [hello, yellow, bell]).

% float32 has 24 bits of precision: 1.0e7 < 2^24, so 1.0e7 + 1 is exact.
test(floats) :-
    example(floats, Values),
    assertion(Values == [1.0e8, 3.0e38]).

test(label_pairs) :-
    example(label_pairs, Pairs),
    assertion(Pairs == [1-4, 2-3, 3-2, 4-1]).

test(label_square_root) :-
    example(label_square_root, Q),
    assertion(Q = algebraic(_, root([-2, 0, 1], 2))).

test(label_colorings) :-
    example(label_colorings, ways(N)),
    assertion(N == 6).

test(schedule) :-
    example(schedule, Schedules),
    msort(Schedules, Sorted),
    assertion(Sorted == [[a, c, b]-[10, 12, 14], [b, c, a]-[9, 11, 13], [c, a, b]-[9, 11, 13], [c, b, a]-[9, 11, 13]]).

test(explain) :-
    example(explain, [A, B]),
    assertion(A = (_ > 10)), assertion(B = (_ < 5)).

:- end_tests(attributed_variable_examples).
