%%% -*- mode: Prolog; Module: z3_utils; -*-.

:- module(z3_utils, [
              add_attribute/2,
              ground_version/3,
              print_declarations/1,
              remove_type_annotations/2,
              reset_var_counts/0,  % internal attribute variables count
              valid_status/1,
              valid_status_list/1,
              z3_declare/3,
              z3_declare_types_for_symbols/3,
              z3_enum_declarations_assoc/2,
              z3_expand_term/2                 % +formula, -formula   Transforms terms before giving them to the C API
          ]).

/** <module> z3_utils

Utilities shared by z3.pl and stateful_repl.pl

*/

:- use_module(library(assoc)).

:- use_module(z3_swi_foreign).

:- use_module(type_inference, [
                  typecheck/4,
                  mappable_symbol/1
                  ]).

:- initialization(reset_var_counts).

mk_uninterpreted(X) :- (var(X) -> X = uninterpreted ; true ).
ground_arglist(L) :- maplist(mk_uninterpreted, L).

%%%%% Attribute (Prolog) variables %%%%%%%%%%

reset_var_counts :- nb_setval(varcount, 0).

inc_var_count(X) :- nb_getval(varcount, X),
                    New is X + 1,
                    nb_setval(varcount, New).

add_attribute(V, Attr) :- var(V),
                          get_attr(V, z3, Attr), !, %  equality should already be asserted
                          true.
add_attribute(V, Attr) :- var(V),
                          inc_var_count(Count),
                          atom_concat(v_, Count, Attr),
                          put_attr(V, z3, Attr).


%% goes through a list of symbols and declares them in Z3, using z3_declare:

z3_declare_types_for_symbols(H, L, M) :-
    maplist({H,M}/[X]>>(get_assoc(X, M, Def) -> z3_declare(H, X, Def) ; true), L).

%! z3_declare(+F:T)
%  calls z3_declare(F, T). "F:T" is used to require the type of F to be T.

%! z3_declare(+F, +T)
%  updates the internal (C code) Z3 declaration map.
%  Unknown types are considered to be uninterpreted.

z3_declare(H, F:T) :- z3_declare(H, F, T). %% take care of explicit types
z3_declare(H, F/0, T) :- !, z3_declare(H, F, T).
z3_declare(H, F, T) :- var(F), !,
                       add_attribute(F, Attr),
                       z3_declare(H, Attr, T).
z3_declare(_, F, int) :- integer(F), !, true.
z3_declare(_, F, real) :- float(F), !, true.
z3_declare(H, F, T) :- atom(T), !,
                       z3_declare_function(H, F, T).
z3_declare(H, F, T) :- compound(T),
                    functor(T, bv, 1), !,
                    must_be(ground, T),
                    z3_declare_function(H, F, T).
z3_declare(H, F, T) :- var(T), !,
                    T = uninterpreted,
                    z3_declare_function(H, F, T).
z3_declare(H, F, lambda(Arglist, Range)) :- (var(F) -> type_error(nonvar, F) ; true), !,
                                            F = F1/N,
                                            length(Arglist, Len),
                                            assertion(N == Len),
                                            ground_arglist(Arglist),
                                            Fapp =.. [F1|Arglist],
                                            (var(Range) -> Range = uninterpreted ; true), !,
                                            z3_declare_function(H, Fapp, Range).


%! ground_version(+Term, -GroundTerm, -SymbolList)
%  Grounds any variables in X by making them into attribute variables,
%  and also returns the non-built-in symbols that it finds, using f/N for all arities, including 0.
%  Using F/N allows overloading by arity.

ground_version(X, Attr, [Attr/0]) :- var(X), !, add_attribute(X, Attr).
ground_version(X, X, S) :- number(X), !, ord_empty(S).
ground_version(X, X, [X/0]) :- atom(X), mappable_symbol(X), !, true.
ground_version(X, X, S) :- atomic(X), !, ord_empty(S).
ground_version(C, XG:T, Result) :- compound(C), C = X:T, !,
                                   %% type checking can instantiate the types, so we don't require them to be ground at this point.
                                   %% (ground(T) -> true ; type_error(ground, T)),
                                   ground_version(X, XG, Result).
ground_version(X, G, Result) :- compound(X),
                                functor(X, F, Arity),
                                X =.. [F|Rest],
                                ground_list(Rest, Grest, R),
                                G =.. [F|Grest],
                                (mappable_symbol(F) ->
                                    ord_add_element(R, F/Arity, Result)
                                ;
                                Result = R).
ground_version([], [], []).


%! remove_type_annotations(+Term, -TermOut)
%  Removes all F:T type annotations from Term.

remove_type_annotations(X, X) :- atomic(X), !.
remove_type_annotations(X:_T, X1) :- mapargs(remove_type_annotations, X, X1), !.
remove_type_annotations(F, F1) :- compound(F), !, mapargs(remove_type_annotations, F, F1).

ground_list([], [], S) :- ord_empty(S).
ground_list([F|Rest], [FG|Grest], Result) :- ground_version(F, FG, GFG), ground_list(Rest, Grest, Arest), ord_union(GFG, Arest, Result).

valid_status_list([l_true, l_false, l_undef, l_type_error]).
valid_status(X) :- valid_status_list(L), member(X, L).


%! Prints declarations for formulas asserted so far, as Z3 ast maps.
%  Can be used to see the declarations used in the previous z3.pl query (reset on a new z3.pl push).

print_declarations(H) :-
    current_output(Out),
    z3_declarations_string(H, S),
    writeln(Out, S),
    z3_enums_string(H, S2),
    writeln(Out, S2).


add_enums([], M, M).
add_enums([Pair | Rest], Min, Mout) :-
    Pair =.. [_, (F/0) , Type], % allow any functor as long as it's arity 2
    typecheck(F, Type, Min, Mnew),
    add_enums(Rest, Mnew, Mout).

%! Creates a typechecking (assoc) map with the current enum declarations.
%  Used to initialize the typechecking map in the presence of enums.
z3_enum_declarations_assoc(H, M) :-
    z3_enum_declarations(H, L),
    add_enums(L, t, M).                                   

expand_macros(F, R) :- functor(F, isoneof, _N), !,
                       F =.. [isoneof | [X | Rest]],
                       maplist({X}/[V,X=V]>>true, Rest, L),
                       R =.. [or | L].
expand_macros(F, R) :- functor(F, alldifferent, _N), !,
                       F =.. [alldifferent | Rest],
                       R =.. [distinct | Rest].
%% The Prolog C interface does not have a way to deconstruct rationals.
%% One solution is to do it here. Another is to call Prolog from the C code, see z3_swi_foreign.c
expand_macros(F, R) :- fail,
                       \+ integer(F),
                       rational(F, A, B), !,
                       R = mk_rational(A,B).

z3_expand_term(A,B) :- mapsubterms(expand_macros,A,B).

:- begin_tests(z3_utils_tests).

test(ground_version, true(Symbols == [a/0, b/0, c/0, f/1, g/0]) ) :-
    F = and(a:int, b = c, or(f(a) = g)),
    ground_version(F, FG, Symbols),
    assertion(F == FG),
    true.

test(remove_type_annotations, true(FN=and(a, b = c))) :-
    F = and(a:int, b = c:real),
    remove_type_annotations(F, FN).

test(declare_lambda, [true(X==uninterpreted)]) :-
    z3_new_handle(H),
    z3_declare(H, f/1, lambda([X], real)),
    z3_free_handle(H).

test(expand) :-
    z3_expand_term(isoneof(x,a,b), or(x=a,x=b)).

:- end_tests(z3_utils_tests).
