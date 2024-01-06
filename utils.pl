%%% -*- Mode: Prolog; Module: utils; -*-

:- module(utils, [
    split_list/3
    ] ).


% split list in half:
split_list(L, A, B) :- length(L, N),
    Half is N div 2,
    Rest is N - Half,
    length(A, Half),
    length(B, Rest),
    append(A, B, L).


