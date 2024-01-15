%%% -*- Mode: Prolog; Module: quickexplain; -*-

% SWI Prolog implementation of Junker's Quickxplain,
% for finding minimally unsatisfiable subsets, and maximally satisfiable ones.

:- module(quickexplain, [
	      qexplain/3,
	      qexplain/4,
	      qrelax/3,
	      qrelax/4
	  ]).

:- meta_predicate qexplain(1, ?, ?).
:- meta_predicate qexplain(1, ?, ?, ?).
:- meta_predicate qrelax(1, ?, ?).
:- meta_predicate qrelax(1, ?, ?, ?).

:- use_module(utils).

% Both explain and relax assume that Base + Constraints are, together, inconsistent; if they are not, Output = Constraints:

qexplain(_Assert, _Base, [], Output) :- !, Output = [].
qexplain(Assert, Base, Constraints, Output) :-
    rec_qexplain(Assert, Base, Base, Constraints, Output).

qexplain(Assert, Constraints, Result) :- qexplain(Assert, [], Constraints, Result).

%% non_empty(Delta) is there to avoid an extra consistency check at the start.
rec_qexplain(Assert, B, Delta, C, Output) :-
    ((non_empty(Delta), inconsistent(Assert, B)) -> Output = [] ; (
        C = [_Alpha] -> Output = C ; (
            split_list(C, C1, C2),
            append(B, C1, B1),
            rec_qexplain(Assert, B1, C1, C2, Delta2),
            append(B, Delta2, B2),
            rec_qexplain(Assert, B2, Delta2, C1, Delta1),
            append(Delta1, Delta2, Output)
        )
    )).

qrelax(_Assert, _B, [], Result) :- !, Result = [].
qrelax(Assert, B, Constraints, Result) :-
    rec_qrelax(Assert, B, Constraints, Result).

qrelax(Assert, Constraints, Result) :- qrelax(Assert, [], Constraints, Result).

rec_qrelax(Assert, B, C, Result) :-
    %% debuginfo("calling rec_qrelax ", info{base:B, constraints:C})
    (C == [] -> Result = [] ;
    (consistent(Assert, B, C) -> (Result = C); (
     C = [_Alpha] -> Result = [] ; (
        split_list(C, C1, C2),
        rec_qrelax(Assert, B, C2, Delta1),
        append(B, Delta1, B2),
        rec_qrelax(Assert, B2, C1, Delta2),
        append(Delta1, Delta2, Result)
        )))).

inconsistent(Assert, L) :- \+ checksat(Assert, L).
consistent(Assert,L) :- \+ \+ checksat(Assert, L).

consistent(Assert, L1, L2) :- \+ \+ checksat(Assert, L1, L2).

checksat(Assert, L) :-
    debuginfo("Calling checksat/2"),
    maplist({Assert}/[X]>>assert_constraint(Assert, X), L),
    true.

checksat(Assert, L1, L2) :- 
        debuginfo("Calling checksat/3"),
        maplist({Assert}/[X]>>assert_constraint(Assert, X), L1),
        maplist({Assert}/[X]>>assert_constraint(Assert, X), L2),
        % term_variables((L1,L2),Variables),
        % labeling(Variables),
        true.

assert_constraint(Assert, Constraint) :-
    debuginfo("Asserting constraint ", Constraint),
    apply(Assert,[Constraint]),
    debuginfo("Succeeded asserting ", Constraint).

non_empty([]) :- fail.
non_empty([_|_]) :- true. 
 
debuginfo(X) :- writeln(X), flush_output.
debuginfo(X, Y) :- write(X), writeln(Y), flush_output.

%% TODO: add tests using CLP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% unit tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(quickexplain_tests).
:- use_module(library(clpfd)).

test(explain1) :-
    qrelax(call, [member(X, [1,2,3,4,5])], [X > 30, X > 2, X >= 4], R),
    R =@= [X>2, X>=4].

test(explain11) :-
    qrelax(call, [X in 1..3], [X #> 30, X#>2, X#>=4], R),
    R = [X #> 2].

test(explain2) :-
    qexplain(call,[X in 1..5], [X=1, X=2, X>1], R),
    R = [X=1, X=2].

test(explain2) :-
    qexplain(call, [member(X,[1,2,3,4,5])], [X=1, X=2, X>1, X < 0], R),
    R = [X=1, X=2].

test(explain3) :-
    qexplain(call, [member(X,[1,2,3,4,5])], [X=1, X < 0, X=2, X>1], R),
    R = [X<0].

% test(myrelax1) :- qexplain(call, [#>((X + Y) , 10)], [(X #< 5), (Y #< 5), (X #> 2), (X #> 4)], R), R =@= [X#<5, Y#<5]

%% todo, add:
% test_explain(call, [{a:int = Y} , Y in 1..6, {Z = a:int}, Z in 6..8, label([Y,Z]), {Y:int > Z:int}],R).
% test_explain(call, [{a:int = Y} , Y in 1..5, {Z = a:int}, Z in 6..8, label([Y,Z]), {Y:int > Z:int}],R).

:- end_tests(quickexplain_tests).
