%%% -*- Mode: Prolog; Module: type_inference; -*-

:- module(type_inference, [
              typecheck/3,
              typecheck/4,
              typecheck_formula_list/3, % convenience
              typecheck_to_list/3, % convenience
              mappable_symbol/1, % true if arg is not a pre-declared atom or function symbol
              algebraic_value/1, % true for an algebraic(Approx, root(Coefficients, Index)) number
              quantifier/3       % quantifier(+Q, -BoundVariables, -Body) for forall/2 and exists/2
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

%% F has been defined:
declared(F) :- signature(F, _, _).
declared(F) :- comparison_operator(F).
declared(F) :- arithmetic_operator(F).
declared(between).
declared(const_array).
declared(forall).
declared(exists).

%! signature(?Functor, ?ArgTypes, ?Result) is nondet.
%  Types of the built-in functions and predicates that are not typed by a rule in typecheck/4.
%  ArgTypes is a list of argument types, all(T) for any number of arguments of type T, or
%  allthen(T, U) for any number of arguments of type T followed by one of type U.
%  Several facts for one Functor give alternative typings, tried in order.

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

signature(=, [T, T], bool).
% for more flexible arithmetic:
% signature(=, [bool, real], bool). % not allowed by Z3
% signature(=, [bool, int], bool). % not allowed by Z3
signature(=, [real, int], bool). % works in Z3
signature(=, [int, real], bool).
signature(<>, [T, T], bool).
signature(<>, [int, real], bool).
signature(<>, [int, bool], bool).
signature(<>, [real, int], bool).
signature(<>, [real, bool], bool).
signature(<>, [bool, real], bool).
signature(<>, [bool, int], bool).

% between/3 is typed by a rule in typecheck/4: its three arguments are numeric, in any combination.

signature(distinct, all(_T), bool).


% +, *, - and minus are typed by a rule in typecheck/4 (see arithmetic_operator/1), not by signatures.

signature(power, [int, int], int).
signature(power, [real, int], real).
signature(power, [int, real], real).
signature(power, [real, real], real).

signature(real2int, [real], int).
signature(int2real, [int], real).
signature(is_int, [real], bool).

% From the Z3 docs:
% "The arguments must either both have int type or both have real type. If the arguments have int type, then the result type is an int type, otherwise the the result type is real."
signature(div, [real, real], real).
signature(div, [int, int], int).
signature(div, [real, int], real).
signature(div, [int, real], real).

signature(divides, [int, int], bool).
signature(rem, [int, int], int).
signature(mod, [int, int], int).

% Comparisons (<, >, =<, >=, leq, geq) are typed by a rule in typecheck/4 (see comparison_operator/1).
signature(and, all(bool), bool).
signature(or, all(bool), bool).
signature(xor, all(bool), bool).
signature(implies, [bool, bool], bool).
signature(iff, [bool, bool], bool).
signature(not, [bool], bool).
signature(true, [], bool).
signature(false, [], bool).
signature(ite, [bool, T, T], T).

%%%% Bit-vector declarations
signature(bv2int, [bv(_N),bool], int).
%% Note that bv2int and int2bv are not supported by the decision procedures.

%%%% use "bool_const" instead of bool in the no_overflow defs that have a bool arg?

signature(bvadd, [bv(N), bv(N)], bv(N)).
signature(bvadd_no_overflow, [bv(N), bv(N), bool], bool).
signature(bvadd_no_underflow, [bv(N), bv(N)], bool).
signature(bvand, [bv(N), bv(N)], bv(N)).
signature(bvashr, [bv(N), bv(N)], bv(N)).
signature(bvlshr, [bv(N), bv(N)], bv(N)).
signature(bvmul, [bv(N), bv(N)], bv(N)).
signature(bvmul_no_overflow, [bv(N), bv(N), bool], bool).
signature(bvmul_no_underflow, [bv(N), bv(N)], bool).
signature(bvnand, [bv(N), bv(N)], bv(N)).
signature(bvneg, [bv(N)], bv(N)).
signature(bvneg_no_overflow, [bv(_N)], bool).
signature(bvnor, [bv(N), bv(N)], bv(N)).
signature(bvnot, [bv(N)], bv(N)).
signature(bvor, [bv(N), bv(N)], bv(N)).
signature(bvredand, [bv(_N)], bv(1)).  % reductions give a single bit
signature(bvredor, [bv(_N)], bv(1)).
signature(bvsdiv, [bv(N), bv(N)], bv(N)).
signature(bvsdiv_no_overflow, [bv(N), bv(N)], bool).
signature(bvsge, [bv(N), bv(N)], bool).
signature(bvsgt, [bv(N), bv(N)], bool).
signature(bvshl, [bv(N), bv(N)], bv(N)).
signature(bvsle, [bv(N), bv(N)], bool).
signature(bvslt, [bv(N), bv(N)], bool).
signature(bvsmod, [bv(N), bv(N)], bv(N)).
signature(bvsrem, [bv(N), bv(N)], bv(N)).
signature(bvsub, [bv(N), bv(N)], bv(N)).
signature(bvsub_no_overflow, [bv(N), bv(N)], bool).        % as Z3_mk_bvsub_no_overflow
signature(bvsub_no_underflow, [bv(N), bv(N), bool], bool). % as Z3_mk_bvsub_no_underflow; bool: signed
signature(bvudiv, [bv(N), bv(N)], bv(N)).
signature(bvuge, [bv(N), bv(N)], bool).
signature(bvugt, [bv(N), bv(N)], bool).
signature(bvule, [bv(N), bv(N)], bool).
signature(bvult, [bv(N), bv(N)], bool).
signature(bvurem, [bv(N), bv(N)], bv(N)).
signature(bvxnor, [bv(N), bv(N)], bv(N)).
signature(bvxor, [bv(N), bv(N)], bv(N)).

%% the result type depends on the value of an arg, so can't quite do this:
%% signature(int2bv, [int, int], bv(_N)).

% atleast and atmost take any number of bools followed by an int:

signature(atleast, allthen(bool, int), bool).
signature(atmost, allthen(bool, int), bool).

% isoneof(x, v1, v2, ...) is expanded to (x = v1 or x = v2 or ...) before typechecking, but typing it
% directly gives the same result:
signature(isoneof, all(_T), bool).

signature(mk_rational, [int, int], real).

%%%% Strings (argument orders as in SMT-LIB)
signature(str_concat, all(string), string).
signature(str_len, [string], int).
signature(str_substr, [string, int, int], string).        % (s, offset, length)
signature(str_at, [string, int], string).                 % the one-character string at an index
signature(str_contains, [string, string], bool).          % (container, containee)
signature(str_prefixof, [string, string], bool).          % (prefix, s)
signature(str_suffixof, [string, string], bool).          % (suffix, s)
signature(str_indexof, [string, string, int], int).       % (s, substring, start); -1 if absent
signature(str_replace, [string, string, string], string). % (s, from, to), first occurrence
signature(str_lt, [string, string], bool).                % lexicographic
signature(str_le, [string, string], bool).
signature(str_to_int, [string], int).                     % -1 unless all digits
signature(int_to_str, [int], string).                     % "" for negative numbers

%%%% Arrays (const_array/2 is typed by a rule in typecheck/4, since its first argument is a sort)
signature(select, [array(I, V), I], V).                   % (array, index)
signature(store, [array(I, V), I, V], array(I, V)).       % (array, index, value)

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


%! quantifier(@Term, -Vars, -Body) is semidet.
%  True if Term is forall(Vars, Body) or exists(Vars, Body), with Vars a list of bound variables:
%  names, each optionally annotated with a sort (x, or x:int).
quantifier(T, Vars, Body) :- compound(T), compound_name_arity(T, Q, 2), memberchk(Q, [forall, exists]),
                             arg(1, T, Vars), is_list(Vars), arg(2, T, Body).

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
typecheck(true, bool, E, E) :- !.
typecheck(false, bool, E, E) :- !.
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
%% bv_numeral(Bits): a bit vector from a list of bits, least significant first, each one of
%% true, false, 1 or 0 (what the C code accepts).
%% Q: how to refer to or constrain a single bit in a BV?
typecheck(T, Type, E, E) :- functor(T, bv_numeral, 1), !,
                            T = bv_numeral(L),
                            is_list(L),
                            L \== [],
                            forall(member(B, L), ( nonvar(B), memberchk(B, [true, false, 1, 0]) )),
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
% const_array(IndexSort, Value): the array with Value at every index.
typecheck(const_array(IndexSort, Value), Type, Envin, Envout) :- !,
                                     ground(IndexSort),
                                     Type = array(IndexSort, ValueType),
                                     typecheck(Value, ValueType, Envin, Envout).
% forall(Vars, Body) and exists(Vars, Body): Body is typed with each bound variable in scope, shadowing
% any constant of the same name; afterwards, each name means again what it meant before (or nothing).
% An annotated variable (x:int) has that sort; for an unannotated one, the sort is inferred.
typecheck(Q, bool, Envin, Envout) :- quantifier(Q, Vars, Body), !,
                                     bind_variables(Vars, Envin, Inner, Saved),
                                     typecheck(Body, bool, Inner, Inner1),
                                     restore_variables(Saved, Inner1, Envout).
typecheck(between(X, Low, High), bool, Envin, Envout) :- !,
                                     numeric_args([X, Low, High], Envin, Envout).
typecheck(X, T, Envin, Envout) :- atomic_mappable(X), !,
                                  (get_assoc(X/0, Envin, T1) ->
                                       T = T1,
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
% Built-ins with a signature (T is not a variable here: the first clause handles those, and the
% comparison operators have no signature).
typecheck(T, Type, Envin, Envout) :-
    functor(T, F, Arity),
    T =.. [F|Subterms],
    signature(F, ArgTypes, Result),
    check_length(ArgTypes, Arity),
    Type = Result,
    check_signature(Subterms, ArgTypes, Envin, Envout).
                             

comparison_operator(F) :- member(F, [<, >, =<, >=, geq, leq]).

% Puts each bound variable in the map, with its sort (a fresh variable if not annotated). Saved lists
% each name with what it meant before, or none.
bind_variables([], E, E, []).
bind_variables([V|Vs], Ein, Eout, [Name-Old|Saved]) :-
    ( V = Name:Sort -> true ; V = Name ),
    must_be(atom, Name),
    ( get_assoc(Name/0, Ein, OldType) -> Old = type(OldType) ; Old = none ),
    put_assoc(Name/0, Ein, Sort, E1),
    bind_variables(Vs, E1, Eout, Saved).

restore_variables([], E, E).
restore_variables([Name-Old|Saved], Ein, Eout) :-
    ( Old = type(T) -> put_assoc(Name/0, Ein, T, E1) ; del_assoc(Name/0, Ein, _, E1) ),
    restore_variables(Saved, E1, Eout).
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
test(int2bv_expression, [nondet]) :-
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
test(isoneof_bool, [nondet]) :-
    typecheck(isoneof(x, 1, 2), T, M),
    assertion(T == bool),
    assertion(get_assoc(x/0, M, int)).

test(alldifferent_like_distinct, [nondet]) :-
    typecheck(alldifferent(a:int, b, c), T, M),
    assertion(T == bool),
    assertion(get_assoc(c/0, M, int)).

% Coverage of built-ins and special forms that had no direct tests.

% Each Term has the given Type, with the given symbol types.
typing(ite(c, a:int, 2), int, [c/0-bool, a/0-int]).
typing(distinct(a:int, b, c), bool, [b/0-int, c/0-int]).
typing(power(a:real, 2), real, [a/0-real]).
typing(div(a:int, 2), int, [a/0-int]).
typing(div(a:real, 2), real, [a/0-real]).
typing(mod(a:int, 3), int, [a/0-int]).
typing(rem(a:int, 3), int, [a/0-int]).
typing(divides(3, a), bool, [a/0-int]).
typing(xor(p, q, r), bool, [p/0-bool, q/0-bool, r/0-bool]).
typing(atmost(p, q, 1), bool, [p/0-bool, q/0-bool]).
typing(mk_numeral("123", bv(16)), bv(16), []).
typing(mk_unsigned_int64(123, bv(16)), bv(16), []).
typing(bv_numeral([true, false, 1, 0]), bv(4), []).
typing(algebraic(1.4142135623730951, root([-2, 0, 1], 2)), real, []).
typing("a string", string, []).
typing(bvadd(x:bv(8), y), bv(8), [y/0-bv(8)]).
typing(bvsub_no_underflow(x:bv(8), y, s), bool, [y/0-bv(8), s/0-bool]).
typing(bv2int(x:bv(8), true), int, [x/0-bv(8)]).
typing(str_concat("a", s, t), string, [s/0-string, t/0-string]).
typing(str_len(s), int, [s/0-string]).
typing(str_substr(s, i, 2), string, [s/0-string, i/0-int]).
typing(str_contains(s, "x"), bool, [s/0-string]).
typing(str_indexof(s, "x", 0), int, [s/0-string]).
typing(str_replace(s, "a", "b"), string, [s/0-string]).
typing(str_lt(s, "b"), bool, [s/0-string]).
typing(str_to_int(s), int, [s/0-string]).
typing(int_to_str(n), string, [n/0-int]).
typing(select(a:array(int, real), i), real, [a/0-array(int, real), i/0-int]).
typing(store(a:array(int, bool), 1, p), array(int, bool), [p/0-bool]).
typing(const_array(int, 0), array(int, int), []).
typing(select(const_array(bv(8), "s"), b), string, [b/0-bv(8)]).
typing(forall([x:int], f(x) > x), bool, [f/1-lambda([int], int)]).
typing(and(x:bool, exists([x:real], x > 0.0)), bool, [x/0-bool]).   % the outer x keeps its type

test(typings, [forall(typing(Term, Type, Symbols)), nondet]) :-
    typecheck(Term, T, M),
    assertion(T == Type),
    forall(member(S-ST, Symbols), assertion(get_assoc(S, M, ST))).

% These do not type.
ill_typed(ite(c, a:int, b:bool)).          % branches of different types
ill_typed(ite(1, a, b)).                    % condition not boolean
ill_typed(mod(a:real, 2)).                  % mod and rem are integer-only
ill_typed(bvadd(x:bv(8), y:bv(16))).        % different widths
ill_typed(bv_numeral([1, x])).              % a bit that is not a bit
ill_typed(bv_numeral([])).                  % no bits
ill_typed(not(_)).                          % unbound subterms are errors, see below
ill_typed(and(p, 3)).                       % 3 is not a bool
ill_typed(str_len(3)).                      % not a string
ill_typed(str_concat("a", 1)).             % not a string
ill_typed(select(a:array(int, int), "x")).  % index of the wrong sort
ill_typed(store(a:array(int, int), 1, 2.0)). % value of the wrong sort
ill_typed(const_array(_, 0)).               % index sort unknown
ill_typed(forall([x:int], and(x, p))).      % x is not a bool
ill_typed(exists([x:int], x + 1)).          % the body is not a formula

test(ill_typed, [forall(ill_typed(Term))]) :-
    \+ catch(typecheck(Term, _, _), error(instantiation_error, _), fail).

test(unbound_term, [throws(error(instantiation_error, _))]) :-
    typecheck(_, _, _).

% A function name can be used with different arities, each with its own type.
% A quantifier's bound variable is not in the map afterwards.
test(bound_not_in_map, [nondet]) :-
    typecheck(forall([x], g(x) = 1), bool, M),
    assertion(\+ get_assoc(x/0, M, _)),
    assertion(get_assoc(g/1, M, lambda([_], int))).

test(overloading_by_arity, [nondet]) :-
    typecheck(and(f(a:int) = 1, f(a, b:bool) = 2.0), bool, M),
    assertion(get_assoc(f/1, M, lambda([int], int))),
    assertion(get_assoc(f/2, M, lambda([int, bool], real))).

% A symbol keeps one type within a formula: p cannot be a boolean and equal to an integer.
% (Booleans are allowed in arithmetic, so and(p, p + 1 = 2) does type.)
test(symbol_type_conflict, [fail]) :-
    typecheck(and(p, p = 3), bool, _).

:- end_tests(type_inference_tests).
