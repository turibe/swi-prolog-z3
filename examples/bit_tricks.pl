#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: bit_tricks; -*-

%% Bit tricks, proved with bit vectors. Programmers use tricks like x & (x - 1) or branch-free
%% absolute values, and Z3 can check them for every value of a 32-bit word at once: it either proves
%% a trick correct or gives a value where it fails. It can also find bugs, such as the overflowing
%% midpoint of a binary search, and find constants, such as the multiplier a compiler uses to divide
%% by 3.
%%
%% Bit vectors are fixed-width machine words: arithmetic wraps around, as in C. Their operations
%% are bvadd, bvsub, bvmul, bvudiv (unsigned) and bvsdiv (signed), bvand, bvor, bvxor, bvnot, bvneg,
%% the shifts bvshl, bvlshr (logical) and bvashr (arithmetic), and comparisons such as bvult
%% (unsigned) and bvslt (signed). A numeral of width W is int2bv(W, N); to keep the formulas short,
%% the examples write plain numbers, and bits/3 turns them into int2bv(W, N).
%%
%% Models give bit vectors as unsigned numbers; answers about signed values convert them.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/bit_tricks.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/bit_tricks).
%%     ?- example(xor_swap).
%%     ?- run_tests(bit_tricks).

:- module(bit_tricks, [
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
% Helpers.

%! bits(+Width, +Formula, -Expanded) is det.
%  Expanded is Formula with each integer N replaced by the bit vector int2bv(Width, N). Sorts, as in
%  x:bv(32), and int2bv/2 terms are left as they are.
bits(W, N, int2bv(W, N)) :- integer(N), !.
bits(_, T, T) :- \+ compound(T), !.
bits(_, T, T) :- T = int2bv(_, _), !.
bits(W, X:Sort, Y:Sort) :- !, bits(W, X, Y).
bits(W, T, E) :- T =.. [F | Args], maplist(bits(W), Args, EArgs), E =.. [F | EArgs].

%! prove(+Width, +Formula, +Vars, -Answer) is det.
%  Answer is yes if Formula holds for all values of its constants, of Width bits. Otherwise it is
%  counterexample(Values), with Values the constants Vars, as Name = Value, where Formula fails;
%  signed(Vars) gives them as signed numbers.
prove(W, Formula, Vars, Answer) :-
    bits(W, Formula, F),
    (   z3_is_implied(F)
    ->  Answer = yes
    ;   z3_push(not(F)),
        z3_model(M),
        values(W, Vars, M.constants, Values),
        Answer = counterexample(Values)
    ).

values(W, signed(Vars), Constants, Values) :- !,
    findall(V = S, ( member(V, Vars), memberchk(V = U, Constants), signed(W, U, S) ), Values).
values(_, Vars, Constants, Values) :-
    findall(V = U, ( member(V, Vars), memberchk(V = U, Constants) ), Values).

% S is the unsigned W-bit number U read as a two's complement signed number.
signed(W, U, S) :- ( U >= 1 << (W - 1) -> S is U - (1 << W) ; S = U ).

% x is one of the 32 powers of two.
power_of_two(X, PowerOfTwo) :-
    findall(X = P, ( between(0, 31, I), P is 1 << I ), Equations),
    PowerOfTwo =.. [or | Equations].

% ------------------------------------------------------------------------------------------------
% The examples: a question, in words, and the code that answers it.

question(power_of_two,
         "Is x a power of two exactly when x & (x - 1) = 0 (32 bits)?").
question(power_of_two_fixed,
         "Is x a power of two exactly when x != 0 and x & (x - 1) = 0?").
question(lowest_bit,
         "Does x & -x keep just the lowest set bit of x?").
question(xor_swap,
         "Do x ^= y; y ^= x; x ^= y swap x and y, for all values?").
question(midpoint,
         "Binary search takes mid = (lo + hi) / 2, with 0 <= lo <= hi (signed 32 bits). Is mid always in [lo, hi]?").
question(midpoint_fixed,
         "Is mid = lo + (hi - lo) / 2 always in [lo, hi]?").
question(abs,
         "Is (x ^ m) - m, with m = x >> 31 (arithmetic shift), the absolute value of x?").
question(abs_negative,
         "Is that absolute value always at least 0?").
question(average,
         "Is (x & y) + ((x ^ y) >> 1) the average of two unsigned 32-bit numbers, rounded down, even when x + y overflows?").
question(popcount,
         "Does the parallel bit count, with masks 0x55555555, 0x33333333, 0x0F0F0F0F and a multiplication by 0x01010101, count the 1 bits of x?").
question(divide_by_3,
         "To divide an 8-bit x by 3, compilers compute (x * m) >> s instead. With 16-bit arithmetic, what are the smallest s and its m?").

% The classic test fails for 0, which is not a power of two.
answer(power_of_two, Answer) :-
    power_of_two(x, P),
    prove(32, (bvand(x:bv(32), bvsub(x, 1)) = 0) <=> P, [x], Answer).

answer(power_of_two_fixed, Answer) :-
    power_of_two(x, P),
    prove(32, (x:bv(32) <> 0 and bvand(x, bvsub(x, 1)) = 0) <=> P, [x], Answer).

% -x is ~x + 1, so x & -x is y with three properties: a power of two (unless x is 0), a bit of x,
% and the lowest one: x has no bits below it.
answer(lowest_bit, Answer) :-
    Y = bvand(x:bv(32), bvneg(x)),
    power_of_two(Y, P),
    prove(32, implies(x <> 0, P) and bvand(x, Y) = Y and bvand(x, bvsub(Y, 1)) = 0, [x], Answer).

% The three assignments, one after another, as new names for the values.
answer(xor_swap, Answer) :-
    X1 = bvxor(x:bv(32), y:bv(32)),
    Y1 = bvxor(y, X1),
    X2 = bvxor(X1, Y1),
    prove(32, X2 = y and Y1 = x, [x, y], Answer).

% The bug in many binary searches (including Java's, until 2006): lo + hi overflows when both are
% large, and wraps around to a negative number.
answer(midpoint, Answer) :-
    Mid = bvsdiv(bvadd(lo:bv(32), hi:bv(32)), 2),
    prove(32, implies(bvsle(0, lo) and bvsle(lo, hi), bvsle(lo, Mid) and bvsle(Mid, hi)),
          signed([lo, hi]), Answer).

answer(midpoint_fixed, Answer) :-
    Mid = bvadd(lo:bv(32), bvsdiv(bvsub(hi:bv(32), lo), 2)),
    prove(32, implies(bvsle(0, lo) and bvsle(lo, hi), bvsle(lo, Mid) and bvsle(Mid, hi)),
          signed([lo, hi]), Answer).

% m is 0 for x >= 0 and -1 (all ones) for x < 0, when (x ^ m) - m is ~x + 1 = -x.
answer(abs, Answer) :-
    M = bvashr(x:bv(32), 31),
    prove(32, bvsub(bvxor(x, M), M) = ite(bvslt(x, 0), bvneg(x), x), [x], Answer).

% It is the same as -x for negative x, and -x overflows for the most negative number, -2^31.
answer(abs_negative, Answer) :-
    M = bvashr(x:bv(32), 31),
    prove(32, bvsle(0, bvsub(bvxor(x, M), M)), signed([x]), Answer).

% The bits x and y share, plus half of those they do not: no step can overflow. To compare with the
% exact average, x and y are 64-bit numbers below 2^32, so that x + y is exact; the trick's result
% is the same at 32 bits, since none of its values reaches 2^32.
answer(average, Answer) :-
    Average = bvadd(bvand(x:bv(64), y:bv(64)), bvlshr(bvxor(x, y), 1)),
    Limit is 1 << 32,
    prove(64, implies(bvult(x, Limit) and bvult(y, Limit), Average = bvlshr(bvadd(x, y), 1)),
          [x, y], Answer).

% Counting bits in parallel: first in each pair of bits, then in each group of four, then in each
% byte; the multiplication adds the four bytes into the top one. It is compared with a plain sum of
% the 32 bits.
answer(popcount, Answer) :-
    findall(bvand(bvlshr(x:bv(32), I), 1), between(0, 31, I), Bits),
    foldl([B, S0, bvadd(S0, B)]>>true, Bits, 0, Sum),
    X1 = bvsub(x, bvand(bvlshr(x, 1), 0x55555555)),
    X2 = bvadd(bvand(X1, 0x33333333), bvand(bvlshr(X1, 2), 0x33333333)),
    X3 = bvand(bvadd(X2, bvlshr(X2, 4)), 0x0F0F0F0F),
    Count = bvlshr(bvmul(X3, 0x01010101), 24),
    prove(32, Count = Sum, [x], Answer).

% Finding a constant: an m such that the formula holds for every x, with forall. Larger shifts give
% more precision, but x * m must fit in 16 bits; the first shift that works is the answer.
answer(divide_by_3, shift(S)-multiplier(M)) :-
    between(1, 15, S),
    bits(16, forall([x:bv(16)], implies(bvult(x, 256), bvlshr(bvmul(x, m:bv(16)), S) = bvudiv(x, 3))),
         F),
    z3_push(F, Status),
    Status == l_true,
    !,
    z3_model(Model),
    memberchk(m = M, Model.constants).

% ------------------------------------------------------------------------------------------------

:- begin_tests(bit_tricks).

expected(power_of_two, counterexample([x = 0])).
expected(power_of_two_fixed, yes).
expected(lowest_bit, yes).
expected(xor_swap, yes).
expected(midpoint_fixed, yes).
expected(abs, yes).
expected(abs_negative, counterexample([x = -2147483648])).
expected(average, yes).
expected(popcount, yes).
expected(divide_by_3, shift(9)-multiplier(171)).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% Z3 picks the values; check in Prolog that they are a real counterexample.
test(midpoint) :-
    example(midpoint, counterexample([lo = Lo, hi = Hi])),
    assertion(( 0 =< Lo, Lo =< Hi, Hi < 1 << 31 )),
    signed(32, (Lo + Hi) /\ 0xFFFFFFFF, Sum),
    Mid is Sum // 2,                       % bvsdiv rounds toward zero, as // does
    assertion(( Mid < Lo ; Mid > Hi )).

% 171 = ceiling(512 / 3), and it divides every 8-bit number by 3.
test(divide_by_3_check) :-
    forall(between(0, 255, X), assertion((X * 171) >> 9 =:= X // 3)).

:- end_tests(bit_tricks).
