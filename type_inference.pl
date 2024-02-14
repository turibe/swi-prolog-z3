%%% -*- Mode: Prolog; Module: type_inference; -*-

:- module(type_inference, [
              typecheck/3,
              typecheck/4,
              typecheck_formula_list/3, % convenience
              typecheck_to_list/3 % convenience
          ]).

/** <module> Type inference

This is a module for typechecking formulas that will be then asserted in Z3,
without having to declare all of the atom and function types separately.
For example, typecheck( and(a:int = f(b) , b:int = c), bool, R) will infer int type for b, and lambda([int], int) for f.
typechecking "atmost(a,b,c,d, ... ,n)" infers bool types for a,b,c,d... and integer type for n.

Like Z3, we allow comparisons between boolean, ints and reals, so 
typecheck(and(a>b, b>c, c>d, d > 1.0, f(a) = c), bool, Y) will have many solutions. These can be narrowed down
by using "a:int" annotations.

Notes:
       - The mapping is returned as an association map (library(assoc)). which requires keys to be ground.
       - Formulas should therefore be ground.
       - Variables can be supported via attributes, and typechecking the ground formula where the variables are replaced by their attributes.
       - We allow overloading by arity.

@author Tomas Uribe
@license MIT

***/


:- license(mit).
:- expects_dialect(swi).


:- use_module(library(assoc)).

%% Note that assoc lists require ground keys.
%% When typing a var, we can add an attribute to it, and then type the attribute.

:- dynamic signature/3.

:- retractall(signature(_,_,_)).

%% F has been defined:
declared(F) :- signature(F, _, _).
declared(F) :- comparison_operator(F).

declare(Functor, ArgTypes, Result) :-
    must_be(atomic, Functor),
    assert(signature(Functor, ArgTypes, Result)).

%% aliases:
signature(/, A, B) :- signature(div, A, B).
signature(==, A, B) :- signature(=, A, B).
signature(equal, A, B) :- signature(=, A, B).
signature(',', A, B) :- signature(and, A, B).
signature(; , A, B) :- signature(or, A, B).
signature(-> , A, B) :- signature(implies, A, B).
signature(<=> , A, B) :- signature(iff, A, B).

% Notation: "all(T)" means there can be an arbitrary number of arguments, all of type T.

:- declare(=, [T, T], bool).
:- declare(<>, [T, T], bool).
:- declare(distinct, all(_T), bool).

% A possible improvement is to support expressions like all(number) AND oneof(float),
% but makes the typechecking more expensive:
% :- declare(+, oneof(real), real).
% :- declare(*, oneof(real), real).

:- declare(+, all(T), T).
:- declare(*, all(T), T).
:- declare(-, [T, T], T).

:- declare(+, [real, _T], real).
:- declare(+, [_T, real], real).
:- declare(*, [real, _T], real).
:- declare(*, [_T, real], real).
:- declare(-, [_T, real], real).
:- declare(-, [real, _T], real).

:- declare(+, [int, bool], int).
:- declare(+, [bool, int], int).
:- declare(+, [bool, bool], int).

:- declare(*, [int, bool], int).
:- declare(*, [bool, int], int).
:- declare(*, [bool, bool], int).

:- declare(power, [int, int], int).
:- declare(power, [real, int], real).
:- declare(power, [_T, real], real).

% From the Z3 docs:
% "The arguments must either both have int type or both have real type. If the arguments have int type, then the result type is an int type, otherwise the the result type is real."
:- declare(div, [real, real], real).
:- declare(div, [int, int], int).
:- declare(div, [real, int], real).
:- declare(div, [int, real], real).

% :- declare(<, [T, T], bool).
% :- declare(>, [T, T], bool).
% :- declare(>=, [T, T], bool).
% :- declare(geq, [T, T], bool).
% :- declare(=<, [T, T], bool).
% :- declare(leq, [T, T], bool).
:- declare(and, all(bool), bool).
:- declare(or, all(bool), bool).
:- declare(xor, all(bool), bool).
:- declare(implies, [bool, bool], bool).
:- declare(iff, [bool, bool], bool).
:- declare(not, [bool], bool).
:- declare(true, [], bool).
:- declare(false, [], bool).
:- declare(ite, [bool, T, T], T).

% atleast and atmost take any number of bools followed by an int:

:- declare(atleast, allthen(bool, int), bool).
:- declare(atmost, allthen(bool, int), bool).

sub_type(int, real).
sub_type(bool, int).
sub_type(bool, real).
sub_type(T,T).

%% unify_or_error(T1, T2) :- T1 = T2, !, true.
%% unify_or_error(T1, T2) :- write(user_error, "Could not unify "), writeln(user_error, types(T1,T2)), fail.

% "mappable" are non-declared atoms or functions whose type signature needs to be inferred; that is, not pre-defined.
atomic_mappable(X) :- atom(X).

compound_mappable(X, N) :- compound(X),
                           functor(X, F, N),
                           \+ declared(F).

check_length(all(_), _) :- !, true.
check_length(allthen(_,_), _) :- !, true.
check_length(L, Arity) :- length(L, Arity).


%%%%%%%% main predicate: typecheck/4 : +Expression, ~Type, +Environment, -NewEnvironment:

typecheck(F, _, _, _) :- var(F), !, instantiation_error(F).
typecheck(Term:Type, T, Envin, Envout) :- !, Type = T,
                                          typecheck(Term, Type, Envin, Envout).
typecheck(X, int, E, E) :- integer(X), !.
%% We could allow integer constants  to be real, but this leads to duplicate answers.
%% Without this, we must use, e.g., 2.0 instead of 2 when warranted.
%% typecheck(X, real, E, E) :- integer(X).
typecheck(X, real, E, E) :- float(X), !.
typecheck(X, string, E, E) :- string(X), !.
typecheck(X, T, Envin, Envout) :- atomic_mappable(X), !,
                                  (get_assoc(X, Envin, T1) ->
                                       T = T1, %% unify_or_error(T, T1), % print error if this fails
                                       Envin = Envout
                                  ;
                                  (
                                      put_assoc(X, Envin, T, Envout)
                                  )
                                  ).
typecheck(X, Type, Envin, Envout) :- compound_mappable(X,Arity), !,
                                     X =.. [F|Subterms],
                                     (get_assoc(F/Arity, Envin, Funtype) ->
                                          Funtype = lambda(Argtypes, Type),
                                          check_signature(Subterms, Argtypes, Envin, Envout)
                                     ;
                                     length(Argtypes, Arity),
                                     Newtype = lambda(Argtypes, Type),
                                     put_assoc(F/Arity, Envin, Newtype, EnvIntermediate),
                                     check_signature(Subterms, Argtypes, EnvIntermediate, Envout)
                                     ).
% check all the comparators:
typecheck(T, bool, E, ER) :- compound(T),
                             functor(T,F,2),
                             comparison_operator(F),
                             T =.. [F, S1, S2],
                             numeric_type(N1),
                             typecheck(S1, N1, E, E1),
                             numeric_type(N2),
                             typecheck(S2, N2, E1, ER).
typecheck(T, Type, Envin, Envout) :-
    nonvar(T),
    functor(T, F, Arity),
    \+ comparison_operator(F),
    T =.. [F|Subterms],
    signature(F, ArgTypes, Result),
    check_length(ArgTypes, Arity),
    Type = Result,
    %% sub_type(Type, Result),
    check_signature(Subterms, ArgTypes, Envin, Envout).
                             

comparison_operator(F) :- member(F, [<, >, =<, >=, geq, leq]).
numeric_type(T) :- member(T, [int, real, bool]).

check_signature([], allthen(_,_), E, E).
check_signature([Arg], allthen(_,T), Ein, Eout) :- !, typecheck(Arg, T, Ein, Eout).
check_signature([Arg|Rest], allthen(AT,T), Ein, Eout) :- \+ Rest = [],
                                                         typecheck(Arg, AT, Ein, E2),
                                                         check_signature(Rest, allthen(AT,T), E2, Eout).

check_signature([], all(_), E, E).
check_signature([Arg|Rest], all(T), Ein, Eout) :- typecheck(Arg, T, Ein, E2),
                                                  check_signature(Rest, all(T), E2, Eout).
check_signature([], [], E, E).
check_signature([Arg|Rest], [T|TRest], Ein, Eout) :- typecheck(Arg, T, Ein, E2),
                                                     check_signature(Rest, TRest, E2, Eout).

%! typecheck(+Term, -Type, -Out:assoc_list) is nondet.
typecheck(Term, Type, Eout) :- empty_assoc(Empty), typecheck(Term, Type, Empty, Eout).


% Convenience:

% assumes that the list represents a conjunction:
typecheck_formula_list([F|R], Ein, Eout) :- typecheck(F, bool, Ein, Enext),
                                            typecheck_formula_list(R, Enext, Eout).
typecheck_formula_list([], E, E) :- true.

% returns a list instead of an assoc map:
typecheck_to_list(Term, Type, Result) :- empty_assoc(Empty), typecheck(Term, Type, Empty, Eout), assoc_to_list(Eout, Result).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Unit tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(type_inference_tests).

test(basic, [true(Atype == int), nondet]) :-
    typecheck(and(a:int > b, c), bool, Map),
    get_assoc(a, Map, Atype),
    get_assoc(b, Map, int),
    get_assoc(c, Map, bool).

test(conflict1, [fail]) :-
    typecheck(a:int, _, Map),
    typecheck(a, bool, Map, _Mapout).

test(conflict2, [fail]) :-
    typecheck(f(a:int), int, Map),
    typecheck(f(b:bool), int, Map, _Mapout).

test(conflict3, [fail]) :-
    typecheck(f(f(a:int)),bool, _M).

test(nested) :-
    typecheck(f(f(a:int)), int, M),
    get_assoc(f/1, M, lambda([int], int)).

test(nested1, [fail]) :-
    typecheck(f(g(a):int, g(b):bool):int, _X, _M).

test(nested2, [fail]) :-
    typecheck(f(g(a:int):int, g(b:bool)), _X, _M).

test(divtest, [nondet]) :-
    type_inference:typecheck(a = div(x, y), _T, t, M), % choicepoint between int and real
    type_inference:typecheck(a = div(b:real, 2), _T1, M, _M1). % don't need 2.0

test(ftest) :-
    typecheck(f(a):int, int, M),
    get_assoc(f/1, M, lambda([_A], int)).

test(nodottest) :-
    typecheck(f(a):int, int, M),
    \+ get_assoc(:, M, _).

% test(badarity) :-
%    catch(typecheck(not(X,Y), bool, _Map), error(E, _), true),
%    E =@= syntax_error(arity_error(not(X,Y), 2)) .

test(atleast) :-
    typecheck(atleast(a,b,c,d), bool, Map),
    get_assoc(a, Map, bool),
    get_assoc(d, Map, int),
    true.

test(intreal, set(T == [bool, int, real]) ) :-
    typecheck(a>1, bool, t, R),
    get_assoc(a,R,T).

typecheck(bool_plus, all(T == [bool, int]) ) :-
    typecheck((a:int) + b, int, R),
    get_assoc(b, R, T).

typecheck(bool_times, all(T == [bool, int]) ) :-
    typecheck((a:int) * b, int, R),
    get_assoc(b, R, T).

:- end_tests(type_inference_tests).
