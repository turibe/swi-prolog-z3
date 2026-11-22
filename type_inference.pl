%%% -*- Mode: Prolog; Module: type_inference; -*-

:- module(type_inference, [
              typecheck/3,
              typecheck/4,
              typecheck_formula_list/3, % convenience
              typecheck_to_list/3, % convenience
              mappable_symbol/1, % true if arg is not a pre-declared atom or function symbol
              algebraic_value/1  % true for an algebraic(Approx, root(Coefficients, Index)) number
          ]).

/** <module> Type inference for Z3 expressions.

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
declared(F) :- arithmetic_operator(F).
declared(between).

declare(Functor, ArgTypes, Result) :-
    must_be(atomic, Functor),
    assert(signature(Functor, ArgTypes, Result)).

%% aliases:
signature(/, A, B) :- signature(div, A, B).
signature(==, A, B) :- signature(=, A, B).
signature(equal, A, B) :- signature(=, A, B).
signature(equals, A, B) :- signature(=, A, B).
signature(alldifferent, A, B) :- signature(distinct, A, B).
signature(',', A, B) :- signature(and, A, B).
signature(; , A, B) :- signature(or, A, B).
signature(-> , A, B) :- signature(implies, A, B).
signature(<=> , A, B) :- signature(iff, A, B).
signature(**, A, B) :- signature(power, A, B).
signature(^, A, B) :- signature(power, A, B).

% Notation: "all(T)" means there can be an arbitrary number of arguments, all of type T.

:- declare(=, [T, T], bool).
% for more flexible arithmetic:
% :- declare(=, [bool, real], bool). % not allowed by Z3
% :- declare(=, [bool, int], bool). % not allowed by Z3
:- declare(=, [real, int], bool). % works in Z3
:- declare(=, [int, real], bool).
:- declare(<>, [T, T], bool).
:- declare(<>, [int, real], bool).
:- declare(<>, [int, bool], bool).
:- declare(<>, [real, int], bool).
:- declare(<>, [real, bool], bool).
:- declare(<>, [bool, real], bool).
:- declare(<>, [bool, int], bool).

% between/3 is typed by a rule in typecheck/4: its three arguments are numeric, in any combination.

:- declare(distinct, all(_T), bool).

% A possible improvement is to support expressions like all(number) AND oneof(float),
% but makes the typechecking more expensive:
% :- declare(+, oneof(real), real).
% :- declare(*, oneof(real), real).

% +, *, - and minus are typed by a rule in typecheck/4 (see arithmetic_operator/1), not by signatures.

:- declare(power, [int, int], int).
:- declare(power, [real, int], real).
:- declare(power, [int, real], real).
:- declare(power, [real, real], real).

:- declare(real2int, [real], int).
:- declare(int2real, [int], real).
:- declare(is_int, [real], bool).

% From the Z3 docs:
% "The arguments must either both have int type or both have real type. If the arguments have int type, then the result type is an int type, otherwise the the result type is real."
:- declare(div, [real, real], real).
:- declare(div, [int, int], int).
:- declare(div, [real, int], real).
:- declare(div, [int, real], real).

:- declare(divides, [int, int], bool).
:- declare(rem, [int, int], int).
:- declare(mod, [int, int], int).

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

%%%% Bit-vector declarations
:- declare(bv2int, [bv(_N),bool], int).
%% Note that bv2int and int2bv are not supported by the decision procedures.

%%%% use "bool_const" instead of bool in the no_overflow defs that have a bool arg?

:- declare(bvadd, [bv(N), bv(N)], bv(N)).
:- declare(bvadd_no_overflow, [bv(N), bv(N), bool], bool).
:- declare(bvadd_no_underflow, [bv(N), bv(N)], bool).
:- declare(bvand, [bv(N), bv(N)], bv(N)).
:- declare(bvashr, [bv(N), bv(N)], bv(N)).
:- declare(bvlshr, [bv(N), bv(N)], bv(N)).
:- declare(bvmul, [bv(N), bv(N)], bv(N)).
:- declare(bvmul_no_overflow, [bv(N), bv(N), bool], bool).
:- declare(bvmul_no_underflow, [bv(N), bv(N)], bool).
:- declare(bvnand, [bv(N), bv(N)], bv(N)).
:- declare(bvneg, [bv(N)], bv(N)).
:- declare(bvneg_no_overflow, [bv(_N)], bool).
:- declare(bvnor, [bv(N), bv(N)], bv(N)).
:- declare(bvnot, [bv(N)], bv(N)).
:- declare(bvor, [bv(N), bv(N)], bv(N)).
:- declare(bvredand, [bv(_N)], bv(1)).  % reductions give a single bit
:- declare(bvredor, [bv(_N)], bv(1)).
:- declare(bvsdiv, [bv(N), bv(N)], bv(N)).
:- declare(bvsdiv_no_overflow, [bv(N), bv(N)], bool).
:- declare(bvsge, [bv(N), bv(N)], bool).
:- declare(bvsgt, [bv(N), bv(N)], bool).
:- declare(bvshl, [bv(N), bv(N)], bv(N)).
:- declare(bvsle, [bv(N), bv(N)], bool).
:- declare(bvslt, [bv(N), bv(N)], bool).
:- declare(bvsmod, [bv(N), bv(N)], bv(N)).
:- declare(bvsrem, [bv(N), bv(N)], bv(N)).
:- declare(bvsub, [bv(N), bv(N)], bv(N)).
:- declare(bvsub_no_overflow, [bv(N), bv(N)], bool).        % as Z3_mk_bvsub_no_overflow
:- declare(bvsub_no_underflow, [bv(N), bv(N), bool], bool). % as Z3_mk_bvsub_no_underflow; bool: signed
:- declare(bvudiv, [bv(N), bv(N)], bv(N)).
:- declare(bvuge, [bv(N), bv(N)], bool).
:- declare(bvugt, [bv(N), bv(N)], bool).
:- declare(bvule, [bv(N), bv(N)], bool).
:- declare(bvult, [bv(N), bv(N)], bool).
:- declare(bvurem, [bv(N), bv(N)], bv(N)).
:- declare(bvxnor, [bv(N), bv(N)], bv(N)).
:- declare(bvxor, [bv(N), bv(N)], bv(N)).

%% the result type depends on the value of an arg, so can't quite do this:
%% :- declare(int2bv, [int, int], bv(_N)).

% atleast and atmost take any number of bools followed by an int:

:- declare(atleast, allthen(bool, int), bool).
:- declare(atmost, allthen(bool, int), bool).

% isoneof(x, v1, v2, ...) is expanded to (x = v1 or x = v2 or ...) before typechecking, but typing it
% directly gives the same result:
:- declare(isoneof, all(_T), bool).

:- declare(mk_rational, [int, int], real).

sub_type(int, real).
sub_type(bool, int).
sub_type(bool, real).
sub_type(T,T).

% unify_or_error(T1, T2) :- T1 = T2, !, true.
% unify_or_error(T1, T2) :- write(user_error, "Could not unify "), writeln(user_error, types(T1,T2)), fail.

% "mappable" are non-declared atoms or functions whose type signature needs to be inferred; that is, not pre-defined.
atomic_mappable(X) :- atom(X).

compound_mappable(X, N) :- compound(X),
                           functor(X, F, N),
                           \+ declared(F).

%! mappable_symbol(+Atom)
%  True iff the type for Atom should be inferred, that is, it is not a pre-declared constant or function.
mappable_symbol(X) :- must_be(atom,X), \+ declared(X). %% note that declared applies to true and false

check_length(all(_), _) :- !, true.
check_length(allthen(_,_), _) :- !, true.
check_length(L, Arity) :- length(L, Arity).


%! algebraic_value(@Term) is semidet.
%  True if Term has the form of an algebraic number, algebraic(Approx, root(Coefficients, Index)),
%  as Z3 models return for irrational values. It denotes the Index-th smallest real root of the
%  polynomial with integer Coefficients, lowest degree first; Approx is ignored when the term is
%  given to Z3. Such terms are real constants, not function applications, so their arguments are
%  neither typechecked nor declared. Their contents are checked when they are converted for Z3.
algebraic_value(T) :- compound(T), T = algebraic(_Approx, Root), compound(Root), Root = root(_, _).

%%%%%%%% main predicate: typecheck/4 : +Expression, ~Type, +Environment, -NewEnvironment:

%! typecheck(+Expression, -Type, +InputMap, +OutputMap)
%  Given the types in InputMap, check/infer Type for Expression, and let OutputMap be the resulting type map.
typecheck(F, _, _, _) :- var(F), !, instantiation_error(F).
typecheck(Term:Type, T, Envin, Envout) :- !, Type = T,
                                          typecheck(Term, Type, Envin, Envout).
typecheck(X, int, E, E) :- integer(X), !.
typecheck(true, bool, E, E) :- true, !.
typecheck(false, bool, E, E) :- true, !.
%% We could allow integer constants  to be real, but this leads to duplicate answers.
%% Without this, we must use, e.g., 2.0 instead of 2 when warranted.
%% typecheck(X, real, E, E) :- integer(X).
typecheck(X, real, E, E) :- float(X), !.
%% introduce a rational type?
typecheck(X, real, E, E) :- rational(X), \+ integer(X), !.
typecheck(X, string, E, E) :- string(X), !.
typecheck(X, real, E, E) :- algebraic_value(X), !.
typecheck(T, bv(N), Envin, Envout) :- functor(T, int2bv, _), !,
                             T = int2bv(N, I),
                             integer(N), N > 0,
                             typecheck(I, int, Envin, Envout).   % any integer expression, not just a literal
typecheck(T, Type, Envin, Envout) :- functor(T, mk_numeral, N), !,
                                     N = 2,
                                     T = mk_numeral(String, Type),
                                     typecheck(String, string, Envin, Envout).
typecheck(T, Type, Envin, Envout) :- functor(T, mk_unsigned_int64, N), !,
                                     N = 2,
                                     T = mk_unsigned_int64(Integer, Type),
                                     typecheck(Integer, int, Envin, Envout).
%% for bv_numeral, need an integer, and a list of bools.
%% Q: how to refer to or constrain a single bit in a BV?
typecheck(T, Type, E, E) :- functor(T, bv_numeral, 1),
                            T = bv_numeral(L),                          
                            ground(L),
                            %% todo: add check that they're all boolean
                            is_list(L),
                            length(L, N),
                            Type = bv(N).
%% Arithmetic, with any number of arguments: each argument is numeric (bool, int or real), and the
%% result is int, or real if some argument is real. Booleans count as 0 or 1, as in Z3.
%% This is one rule rather than overlapping signatures, so that each typing is found once: with the
%% overlapping signatures, a type error near a long sum of reals took exponential time to report.
typecheck(T, Type, Envin, Envout) :- compound(T), functor(T, F, Arity), Arity >= 1,
                                     arithmetic_operator(F), !,
                                     T =.. [F|Args],
                                     member(Type, [int, real]),
                                     arithmetic_args(Args, Type, Envin, Envout, false, SawReal),
                                     ( Type == real -> SawReal == true ; true ).
typecheck(between(X, Low, High), bool, Envin, Envout) :- !,
                                     numeric_args([X, Low, High], Envin, Envout).
typecheck(X, T, Envin, Envout) :- atomic_mappable(X), !,
                                  (get_assoc(X/0, Envin, T1) ->
                                       T = T1, %% unify_or_error(T, T1), % print error if this fails
                                       Envin = Envout
                                  ;
                                  (
                                      put_assoc(X/0, Envin, T, Envout)
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
arithmetic_operator(F) :- memberchk(F, [+, *, -, minus]).
numeric_type(T) :- member(T, [int, real, bool]).

% Arguments of an arithmetic operation whose result has type Type: an argument's type is at most Type
% (bool < int < real), tried from Type down. SawReal says whether some argument is real.
arithmetic_args([], _, E, E, SawReal, SawReal).
arithmetic_args([A|As], Type, Ein, Eout, SawReal0, SawReal) :-
    arithmetic_arg_type(Type, ArgType),
    typecheck(A, ArgType, Ein, E1),
    ( ArgType == real -> SawReal1 = true ; SawReal1 = SawReal0 ),
    arithmetic_args(As, Type, E1, Eout, SawReal1, SawReal).

arithmetic_arg_type(int, T) :- member(T, [int, bool]).
arithmetic_arg_type(real, T) :- member(T, [real, int, bool]).

numeric_args([], E, E).
numeric_args([A|As], Ein, Eout) :- numeric_type(N), typecheck(A, N, Ein, E1), numeric_args(As, E1, Eout).

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

%! typecheck(+Term, -Type, -OutputMap) is nondet.
%  Checks/infers that Term has Type, starting from an empty map.
typecheck(Term, Type, Eout) :- empty_assoc(Empty), typecheck(Term, Type, Empty, Eout).


% Convenience:

%! typecheck_formula_list(+FormulaList, +MapIn, -MapOut)
%  Convenience, assumes that FormulaList represents a conjunction (all boolean formulas).
typecheck_formula_list([F|R], Ein, Eout) :- typecheck(F, bool, Ein, Enext),
                                            typecheck_formula_list(R, Enext, Eout).
typecheck_formula_list([], E, E) :- true.

%! typecheck_to_list(+Term, -Type, -List)
%  Like typecheck/3 but returns a list instead of an assoc map:
typecheck_to_list(Term, Type, Result) :- empty_assoc(Empty), typecheck(Term, Type, Empty, Eout), assoc_to_list(Eout, Result).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Unit tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(type_inference_tests).

test(basic, [true(Atype == int), nondet]) :-
    typecheck(and(a:int > b, c), bool, Map),
    get_assoc(a/0, Map, Atype),
    get_assoc(b/0, Map, int),
    get_assoc(c/0, Map, bool).

test(conflict1, [fail]) :-
    typecheck(a:int, _, Map),
    typecheck(a/0, bool, Map, _Mapout).

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

test(badarity) :-
    \+ typecheck(not(_X,_Y), bool, _R).

%    catch(typecheck(not(X,Y), bool, _Map), error(E, _), true),
%    E =@= syntax_error(arity_error(not(X,Y), 2)) .

test(atleast) :-
    typecheck(atleast(a,b,c,d), bool, Map),
    get_assoc(a/0, Map, bool),
    get_assoc(d/0, Map, int).

test(intreal, set(T == [bool, int, real]) ) :-
    typecheck(a>1, bool, t, R),
    get_assoc(a/0,R,T).

test(bool_plus, set(T == [bool, int]) ) :-
    typecheck((a:int) + b, int, R),
    get_assoc(b/0, R, T).

test(bool_times, set(T == [bool, int]) ) :-
    typecheck((a:int) * b, int, R),
    get_assoc(b/0, R, T).

test(nested_decl, [true((FT == lambda([int], int), GT=FT)), nondet ]) :-
    typecheck(f(g(a:int):int):int = b:int, bool, t, R),
    get_assoc(f/1, R, FT),
    get_assoc(g/1, R, GT).

test(basic_eq, set(T == [int, real])) :-
    typecheck(a = b:int, bool, t, R),
    get_assoc(a/0, R, T),
    get_assoc(b/0, R, int).

% Number of distinct typings of Term (as Type and map), to check that each is found once.
count_typings(Term, Type, N) :-
    findall(Type-L, (typecheck(Term, Type, M), assoc_to_list(M, L)), Sols),
    length(Sols, N).

% Arithmetic is typed by one rule, so each typing is found once (overlapping signatures used to give
% a:real + b:real three identical typings).
test(arith_typings_once, [forall(member(Term-N, [ (a:real) + (b:real) - 1,
                                                    (a:int) + (b:real) - 1,
                                                    (a:int) * (b:int) - 1,
                                                    -(a:real) - 1,
                                                    +(a:int, b:int, c:real) - 1 ]))]) :-
    count_typings(Term, _, Count),
    assertion(Count == N).

test(arith_result_types, [forall(member(Term-Type, [ (a:int) + (b:real) - real,
                                                       (a:bool) + (b:bool) - int,
                                                       (a:bool) * (b:real) - real,
                                                       minus(a:int, 1) - int,
                                                       +(a:int, b:int, c:real) - real ]))]) :-
    typecheck(Term, T, _),
    !,
    assertion(T == Type).

% An unknown argument can be anything numeric no larger than the result.
test(arith_unknown_arg, set(T == [bool, int, real])) :-
    typecheck((a:real) + b, real, M),
    get_assoc(b/0, M, T).

% Arithmetic needs numbers: it used to accept any sort, and booleans as results.
test(arith_not_numeric, [fail]) :-
    typecheck((a:foo) + b, _, _).

test(arith_no_bool_result, [fail]) :-
    typecheck((a:bool) + (b:bool), bool, _).

% A type error near a long sum used to take exponential time (3 s for 12 terms).
test(arith_type_error_fast) :-
    numlist(1, 20, Is),
    foldl([I, S0, S0 + (V:real)]>>format(atom(V), "x~w", [I]), Is, 0.0, Sum),
    % The time limit makes the old behavior fail the test rather than run for hours.
    catch(call_with_time_limit(2, \+ typecheck(and(Sum > 0.0, p:int = q:bool), bool, _)), E, true),
    assertion(var(E)).

% between/3 takes numeric arguments in any combination; [int, real, real] used to be declared twice,
% and [real, int, int] not at all.
test(between_typings, [forall(member(Term, [ between(a:int, b:real, c:real),
                                             between(a:real, b:int, c:int),
                                             between(a:int, b:int, c:int) ]))]) :-
    count_typings(Term, bool, Count),
    assertion(Count == 1).

test(between_not_numeric, [fail]) :-
    typecheck(between(a:foo, 1, 2), bool, _).

% int2bv used to accept only an integer literal.
test(int2bv_expression) :-
    typecheck(int2bv(8, (b:int) + 1), T, M),
    assertion(T == bv(8)),
    assertion(get_assoc(b/0, M, int)).

test(int2bv_bad_width, [fail]) :-
    typecheck(int2bv(0, 5), _, _).

% Bit reductions give one bit, not a vector of the argument's width.
test(bit_reductions, [forall(member(Op, [bvredand, bvredor]))]) :-
    T =.. [Op, x:bv(8)],
    typecheck(T, Type, _),
    assertion(Type == bv(1)).

% isoneof was declared with a meaningless type; alldifferent had no type at all.
test(isoneof_bool) :-
    typecheck(isoneof(x, 1, 2), T, M),
    assertion(T == bool),
    assertion(get_assoc(x/0, M, int)).

test(alldifferent_like_distinct) :-
    typecheck(alldifferent(a:int, b, c), T, M),
    assertion(T == bool),
    assertion(get_assoc(c/0, M, int)).

:- end_tests(type_inference_tests).
