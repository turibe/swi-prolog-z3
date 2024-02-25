%%% -*- Mode: Prolog; Module: z3_utils; --*

:- module(z3_utils, [
              declare_z3_types_for_symbols/2,
              reset_var_counts/0,
              ground_version/3,
              remove_type_annotations/2,
              valid_status_list/1,
              valid_status/1,
              z3_declare/2,
              add_attribute/2
          ]).

/** <module> z3_utils

Utilities shared by z3.pl and sateful_repl.pl

*/

:- use_module(z3_swi_foreign).

:- use_module(type_inference).

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

declare_z3_types_for_symbols(L, M) :-
    maplist({M}/[X]>>(get_assoc(X, M, Def) -> z3_declare(X,Def) ; true), L).

%! z3_declare(+F:T)
%  calls z3_declare(F, T)

%! z3_declare(+F, +T)
%  updates the internal (C code) Z3 declaration map.
%  Unknown types are considered to be uninterpreted.
z3_declare(F:T) :- z3_declare(F, T). %% take care of explicit types
z3_declare(F/0, T) :- !, z3_declare(F, T).
z3_declare(F, T) :- var(F), !,
                    add_attribute(F, Attr),
                    z3_declare(Attr, T).
z3_declare(F, int) :- integer(F), !, true.
z3_declare(F, real) :- float(F), !, true.
z3_declare(F, T) :- atom(T), !,
                    z3_declare_function(F, T).
z3_declare(F, T) :- compound(T),
                    functor(T, bv, 1), !,
                    must_be(ground, T),
                    z3_declare_function(F, T).
z3_declare(F, T) :- var(T), !,
                    T = uninterpreted,
                    z3_declare_function(F, T).
z3_declare(F, lambda(Arglist, Range)) :- (var(F) -> type_error(nonvar, F) ; true), !,
                                         F = F1/N,
                                         length(Arglist, Len),
                                         assertion(N == Len),
                                         ground_arglist(Arglist),
                                         Fapp =.. [F1|Arglist],
                                         (var(Range) -> Range = uninterpreted ; true), !,
                                         z3_declare_function(Fapp, Range).

% We now allow overloading by arity.

% Grounds any variables in X by making them into attribute variables,
% and also returns the non-built-in symbols that it finds, using f/N for all arities, including 0:

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

remove_type_annotations(X, X) :- atomic(X), !.
remove_type_annotations(X:_T, X1) :- mapargs(remove_type_annotations, X, X1), !.
remove_type_annotations(F, F1) :- compound(F), !, mapargs(remove_type_annotations, F, F1).

ground_list([], [], S) :- ord_empty(S).
ground_list([F|Rest], [FG|Grest], Result) :- ground_version(F, FG, GFG), ground_list(Rest, Grest, Arest), ord_union(GFG, Arest, Result).

valid_status_list([l_true, l_false, l_undef, l_type_error]).
valid_status(X) :- valid_status_list(L), member(X, L).
