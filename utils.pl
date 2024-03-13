%%% -*- Mode: Prolog; Module: utils; -*-

:- module(utils, [
              split_list/3,
              subterm_list/2,
              repeat_string/3,
              readable_bytes/2,
              pair_list_to_assoc/2
    ] ).

/** <module> Basic utils
 
@author Tomas Uribe
@license MIT
*/


%! split_list(+List, -L1, -L2)
%  Split List in half:
split_list(L, A, B) :- length(L, N),
    Half is N div 2,
    Rest is N - Half,
    length(A, Half),
    length(B, Rest),
    append(A, B, L).

%! subterm_list(+Term, -List)
%  Get a list of all the direct subterms of Term
subterm_list(T, L) :- findall(Y, arg(_, T, Y), L).

%! repeat_string(+String, +N, -Result)
%  Result is String repeated N times.
repeat_string(S, N, R) :- must_be(string, S),
                          must_be(integer, N),
                          length(L, N),
                          maplist(=(S), L),
                          atomics_to_string(L, R).

% atomic_list_concat(L, R) % gets an atom

kilo(X) :- X is 1024.
meg(X) :- kilo(K), X is K * 1024.
gig(X) :- meg(M), X is M * 1024.

%! readable_bytes(+Bytes, -String)
%  Generates a human-friendly description of Bytes
readable_bytes(Bytes, Output) :- Bytes < 1024, !, swritef(Output, "%w bytes", [Bytes]).
readable_bytes(Bytes, Output) :- meg(M), Bytes =< M, !, kilo(K), Kilos is Bytes/K, swritef(Output, "%w K", [Kilos]).
readable_bytes(Bytes, Output) :- gig(G), Bytes =< G, !, meg(M), Megs is Bytes/M, swritef(Output, "%w Megs", [Megs]).
readable_bytes(Bytes, Output) :- gig(G),
                                 assertion(Bytes > G), !,
                                 Gigs is Bytes/G,
                                 swritef(Output, "%w Gigs", [Gigs]).

add_pair(Pair, A1, A2) :-
    Pair =.. [_, K, V],
    put_assoc(K,A1,V,A2).

/**
pair_list_to_assoc([], t).
pair_list_to_assoc([X|Rest], M) :- % TODO: better recursion here.
    pair_list_to_assoc(Rest, M1),
    add_pair(X, M1, M).
**/

%! pair_list_to_assoc(+List, -Map)
%  Creates an assoc map from a list of pairs (binary terms, any function symbol is allowed).
pair_list_to_assoc(L, R) :- foldl(add_pair, L, t, R).

:- begin_tests(util_tests).

test(empty) :-
    split_list([], [], []).

test(one) :-
    split_list([a], [], [a]).

test(odd) :-
    split_list([a,b,c,d,e], [a,b], [c,d,e]).

test(even, true(X == [3,4])) :-
    split_list([1,2,3,4], [1,2], X).

test(repeat_string, true(R == "ababab")) :-
    repeat_string("ab", 3, R).

:- end_tests(util_tests).
