%%% -*- Mode: Prolog; Module: memtest; -*-

%% Primitive tool to check for no crashes and no memory leaks.

:- module(memtest, [
              random_test/1
	  ]).


:- use_module(examples/einstein).

:- use_module(z3).


random_test(0) :- true, !.
random_test(N) :- N > 0,
                  random_between(1,6,X),
                  do_test(X),
                  N1 is N - 1,
                  random_test(N1).


myrun(Test) :- write("*********************** "), write(Test), writeln(" *************************"),
               run_tests(Test).


do_test(1) :-
    myrun(z3_swi_foreign).
do_test(2) :-
    true,
    myrun(einstein:no_enums). %% resets globals 
do_test(3) :-
    myrun(einstein:enums), %% cause crashes? We never reset otherwise.
    myrun(push_assert).
do_test(4) :-
    myrun(attribute).
do_test(5) :-
    run_tests(enums), %% cause crashes?
    myrun(boolean).
do_test(6) :-
    %% z3_reset, %% causes crash
    %% z3:z3_reset_context.
    true.

%% myrun(z3_swi_foreign).

