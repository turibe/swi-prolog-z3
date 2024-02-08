%%% -*- Mode: Prolog; Module: type_inference; -*-

/** <module> Type inference

This is a convenience module for typechecking formulas that will be then asserted in Z3,
without having to declare all of the atom and function types.
For example, typecheck(and(a>b, b>c, c>d ,d > 1.0, f(a) = c), X, Y) infers "real" types for a,b,c, and d,
and real->real for the function f.

Typechecking atmost(a,b,c,d, ... ,n) infers bool types for a,b,c,d... and integer type for n.

Notes:
       - The mapping is returned as an association map (library(assoc)). which requires keys to be ground.
       - Formulas should therefore be ground. (Variables could be supported via attributes.)

@author Tomas Uribe
@license MIT

***/

:- module(type_inference, [
              typecheck/3,
              typecheck/4,
              typecheck_formula_list/3, % convenience
	      typecheck_to_list/3 % convenience
          ]).

:- license(mit).
:- expects_dialect(swi).


:- use_module(library(assoc)).


%% Note that assoc lists require ground keys.
%% When typing a var, we can add an attribute to it, and then type the attribute.

:- dynamic signature/3.

% :- initialization(...) ?

:- retractall(signature(_,_,_)).

%% F has been defined:
declared(F) :- signature(F, _, _).

declare(Functor, ArgTypes, Result) :-
    must_be(atomic, Functor),
    assert(signature(Functor, ArgTypes, Result)).

% Notation: "all(T)" means there can be an arbitrary number of arguments, all of type T. 
% A possible improvement is to support expressions like all(number) AND oneof(float).

:- declare(=, [T, T], bool).
:- declare(<>, [T, T], bool).
:- declare(==, [T, T], bool).
:- declare(equal, [T, T], bool).
:- declare(distinct, all(_T), bool).
:- declare(+, all(T), T).

% :- declare(+, oneof(real), real).
% :- declare(+, [real, T], real).
% :- declare(+, [T, real], real).
% :- declare(*, oneof(real), real).

:- declare(*, all(T), T).
:- declare(power, [int, int], int).
:- declare(power, [real, int], real).
:- declare(power, [_T, real], real).
% :- declare(*, [real, T], real).
% :- declare(*, [T, real], real).

% div poses a problem that we can infer int types, but constraints asserted later might imply they are real.
% really need an OR type.
% "The arguments must either both have int type or both have real type. If the arguments have int type, then the result type is an int type, otherwise the the result type is real."
:- declare(div, [real, real], real).
:- declare(div, [int, int], int).

:- declare(/, [real, real], real).
:- declare(/, [int, int], int).
:- declare(-, [T, T], T).
:- declare(<, [T, T], bool).
:- declare(>, [T, T], bool).
:- declare(>=, [T, T], bool).
:- declare(geq, [T, T], bool).
:- declare(=<, [T, T], bool).
:- declare(leq, [T, T], bool).
:- declare(and, all(bool), bool).
:- declare("," , all(bool), bool).
:- declare(; , all(bool), bool).
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

% TODO: use attributed variables with finite domains, to represent cases where a var can be one of several types.



/*******************
% TODO: foldl could do this job?
check_subterm_list([], _Type, E, E).
check_subterm_list([S|Rest], Type, E, Eout) :-
    typecheck(S, Type, E, E1),
    check_subterm_list(Rest, Type, E1, Eout).

typecheck(T, Type, Envin, Envout) :- member(Type, [int, float, bool]),
                                      T =.. [F|Subterms],
                                      functor_type(F, Type),
                                      check_subterm_list(Subterms, Type, Envin, Envout).
********************/



% "mappable" here means a non-declared atom or function whose type signature needs to be inferred --- not one of the pre-defined ones.
atomic_mappable(X, X) :- atom(X), !, true. % we want to exclude int, string, etc., so just atomic won't do.a
% atomic_mappable(X, A) :- var(X), !, z3:add_attribute(X, A).

compound_mappable(X) :- compound(X),
                        functor(X, F, _N),
                        \+ declared(F).


check_length(all(_), _) :- !, true.
check_length(allthen(_,_), _) :- !, true.
check_length(L, Arity) :- length(L, Arity).

% TODO: consider adding a delta?

typecheck(F, _, _, _) :- var(F), !, instantiation_error(F).
typecheck(Term:Type, T, Envin, Envout) :- !, Type = T,  typecheck(Term, Type, Envin, Envout).
% typecheck(Term:T, Type, Envin, Envout) :-  %% confusing rule, get rid of it? Unifies Type and T.
%    atom(Term), !,
%    Type = T,
%    (get_assoc(Term, Envin, Existing) -> (Type = Existing, Envout=Envin) ;
%     put_assoc(Term, Envin, T, Envout)
%     ).
typecheck(T, Type, Envin, Envout) :-
    nonvar(T),
    functor(T, F, Arity),
    T =.. [F|Subterms],
    signature(F, ArgTypes, Result),
    check_length(ArgTypes, Arity),
    Type = Result,
    check_signature(Subterms, ArgTypes, Envin, Envout), !.
typecheck(X, int, E, E) :- integer(X), !.
typecheck(X, real, E, E) :- integer(X), !.
typecheck(X, real, E, E) :- float(X), !.
typecheck(X, string, E, E) :- string(X), !.
typecheck(X1, T, Envin, Envout) :- atomic_mappable(X1, X), !,
                                   (get_assoc(X, Envin, T1) ->
					T = T1, % TODO: print error if this fails
					Envin = Envout
				   ;
                                   put_assoc(X, Envin, T, Envout)
				   ).				   
typecheck(X, Type, Envin, Envout) :- compound_mappable(X), !,
                                     X =.. [F|Subterms],
                                     (get_assoc(F, Envin, Funtype) ->
					  Funtype = lambda(Argtypes, Type),
					  check_signature(Subterms, Argtypes, Envin, Envout)
				     ;
                                     length(Subterms, Arity),
                                     length(Argtypes, Arity),
                                     Newtype = lambda(Argtypes, Type),
                                     put_assoc(F, Envin, Newtype, EnvIntermediate),
                                     check_signature(Subterms, Argtypes, EnvIntermediate, Envout)
				     ).


% TODO: works but want to avoid blowups.
% ideally one would just assert the constraint, check that it's satisfiable, and continue.
% the map would have to support those constraints. Use attributed variables?
% check_signature([], oneof(T), _, _) :- fail.
% check_signature([Arg|Rest], oneof(T), Ein, Eout) :-
%    typecheck(Arg, T, Ein, Eout) -> true ; check_signature(Rest, oneof(T), Ein, Eout).

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

% assumes the list represents a conjunction:
typecheck_formula_list([F|R], Ein, Eout) :- typecheck(F, bool, Ein, Enext),
                                            typecheck_formula_list(R, Enext, Eout).
typecheck_formula_list([], E, E) :- true.

% returns a list instead of an assoc map:
typecheck_to_list(Term, Type, Result) :- empty_assoc(Empty), typecheck(Term, Type, Empty, Eout), assoc_to_list(Eout, Result).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Unit tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(type_inference_tests).

test(basic, [true(Atype == int)]) :-
    typecheck(and(a:int > b, c), bool, Map),
    get_assoc(a, Map, Atype), !,
    get_assoc(b, Map, int), !,
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
    get_assoc(f, M, lambda([int], int)).

test(nested1, [fail]) :-
    typecheck(f(g(a):int, g(b):bool):int, _X, _M).

test(nested2, [fail]) :-
    typecheck(f(g(a:int):int, g(b:bool)), _X, _M).


test(divtest, [nondet]) :-
    type_inference:typecheck(a=div(x, y), _T, t, M), % choicepoint between int and real
    type_inference:typecheck(a = div(b:real, 2), _T1, M, _M1).

test(ftest) :-
    typecheck(f(a):int, int, M),
    get_assoc(f, M, lambda([_A], int)).

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

:- end_tests(type_inference_tests).
