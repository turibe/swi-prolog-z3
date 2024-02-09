%%% -*- Mode: Prolog; Module: z3; -*-

%% This file is included by z3.pl, for additional unit tests:

% :- use_module(z3).

:- begin_tests(z3_pl_tests).

test(findall, [true(R == [a,c]) ] ) :-
    z3_push(f(a:int) = b:int),
    z3_push(f(b) = c:int),
    z3_push(f(c) = a),
    findall(X, (member(X, [a,b,c]), \+ z3_is_implied(f(f(f(f(f(X)))))=a)), R).


test(declare_lambda) :-
    z3_push(a:int>10),
    z3_push(b:int > 12),
    z3_push(a=b),
    z3_declare(f,lambda([int],int)),
    % z3_push_and_print(f(a)>b).
    z3_push(f(a) > b).

test(get_model, [true(C == [(a->13), (b->13), (d->4)] ), true(F == [else(f, 20), (f(4)->5)] )]) :-
    z3_push(a:int > 10),
    z3_push(b:int > 12),
    z3_push(a=b),
    %% z3_declare(f,lambda([int],int)),
    z3_push((f(a) = 20) and (f(d) = 5)),
    z3_push(f(a) > b),
    z3_model_map(_X{constants:C,functions:F}).

%%  f^m(a) = a = f^n(a) ⟹  f^(gcd(m,n))(a) = a

declare_types :-
    z3_declare(f,lambda([int],int)),
    z3_declare(a, int),
    z3_declare(b, int).

%% fpower(F,A,N,-R) makes F(F(...(A))) with nesting of N:
fpower(_F,A,0,A) :- !, true.
fpower(F,A,1,R) :- !, R =..[F,A].
fpower(F,A,N,R) :- N > 1, J is N-1, !, fpower(F,A,J,Z), R=..[F,Z].

%% For a given M and N, X will range over the powers of the GCD of M and N between 1 and max(M,N):
z3gcd(M,N,X) :- fpower(f,a:int,M, Tm),
		fpower(f,a:int, N, Tn),
		z3_push(and(a=Tm,a=Tn)),
		Top is max(M,N),
		between(2,Top,X),
		fpower(f,a,X,Tx),
		z3_is_implied(a=Tx).


test(gcd) :-
    z3gcd(9, 21, 3),
    z3gcd(100, 2100, 100).


test(not_implied, [true(R==l_true)]) :-
    % declare_types, % not needed
    fpower(f,a:int,6,T1),
    fpower(f,a:int,9,T2),
    fpower(f,a:int,3,T3),
    fpower(f,a:int,7,T4),
    z3_push(a=T1), z3_push(a=T2),
    z3_is_implied(T3=T2),
    z3_is_implied(T1=T2),
    \+ z3_is_implied(T1=T4),
    z3_print_status(R).


test(implied) :-
    % declare_types,
    fpower(f,a:int,6,T1),
    fpower(f,a:int,15,T2),
    z3_push(T1=T2),
    z3_push(T1=a),
    fpower(f,a:int,3,T3),
    z3_is_implied(a=T3).

test(conjunction) :-
    z3_push(and(a:int>b,and(b>c,c>d))),
    z3_is_implied(a > d).


test(model) :-
    z3_push(and(f(a) = b, f(b)=c)),
    z3_model_map(_X{constants:C, functions:F}),
    C = [(a->'uninterpreted!val!0'), (b->'uninterpreted!val!1'), (c->'uninterpreted!val!2')],
    F = [else(f, 'uninterpreted!val!1'), (f('uninterpreted!val!1')->'uninterpreted!val!2')].


% consult(swi_relax).

% test_relax(z3_push, [a=1, a=2, a > 1, a = b], R).

% test_explain(z3_push, [a=1, a=2, a > 1, a = b, b= 1], R).


:- end_tests(z3_pl_tests).