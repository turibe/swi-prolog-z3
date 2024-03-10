%%% -*- Mode: Prolog; Module: quickexplain; -*-

:- module(quickexplain, [
              % These assume that Base+Constraints is unsatisfiable:
              qexplain/4, % +AssertPredicate, +Base, +Constraints, -Result
              qexplain/3, % +AssertPredicate, +Constraints, -Result   (empty Base)
              
              qrelax/4,   % +AssertPredicate, +Base, +Constraints, -Result
              qrelax/3,   % +AssertPredicate, +Constraints, -Result   (empty Base)

              % Use these if you want a consistency check at the start:
              top_explain/4,   % +AssertPredicate, +Base, +Constraints, -Result
              top_explain/3,   % +AssertPredicate, +Constraints, -Result   (empty Base)

              top_relax/4,   % +AssertPredicate, +Base, +Constraints, -Result
              top_relax/3    % +AssertPredicate, +Constraints, -Result   (empty Base)

          ]).

/** <module> Quickexplain

SWI Prolog implementation of Ulrich Junker's Quickxplain (https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf),
for finding minimally unsatisfiable subsets, and maximally satisfiable ones.

@author Tomas Uribe
@license MIT
*/

:- meta_predicate qexplain(1, ?, ?).
:- meta_predicate qexplain(1, ?, ?, ?).
:- meta_predicate qrelax(1, ?, ?).
:- meta_predicate qrelax(1, ?, ?, ?).

:- meta_predicate top_explain(1, ?, ?).
:- meta_predicate top_explain(1, ?, ?, ?).
:- meta_predicate top_relax(1, ?, ?).
:- meta_predicate top_relax(1, ?, ?, ?).

:- use_module(utils).

% debuginfo(X) :- writeln(X), flush_output.
% debuginfo(X, Y) :- write(X), writeln(Y), flush_output.
debuginfo(_X) :- true.
debuginfo(_X, _Y) :- true.

%% Both explain and relax assume that Base + Constraints are, together, inconsistent;
%% if they are not, Output = Constraints, which is fine for relax but confusing for explain.
%% use the "top_" procedures to check consistency first.

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

top_explain(Assert, Base, Constraints, Output) :-
    consistent(Assert, Base, Constraints) -> Output = "consistent"; qexplain(Assert, Base, Constraints, Output).
top_explain(Assert, Constraints, Output) :- top_explain(Assert, [], Constraints, Output).

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

top_relax(Assert, Base, Constraints, Output) :-
    consistent(Assert, Base, Constraints) -> Output = "consistent"; qrelax(Assert, Base, Constraints, Output).
top_relax(Assert, Constraints, Output) :- top_relax(Assert, [], Constraints, Output).


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
        % term_variables((L1,L2),Variables), % could have custom checks in the future that do this, complicates the API a little.
        % labeling(Variables),
        true.

assert_constraint(Assert, Constraint) :-
    debuginfo("Asserting constraint ", Constraint),
    apply(Assert,[Constraint]),
    debuginfo("Succeeded asserting ", Constraint).

non_empty([]) :- fail.
non_empty([_|_]) :- true. 
 

%% TODO: add tests using CLP

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% unit tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(quickexplain_tests).
:- use_module(library(clpfd)).

test(explain1) :-
    qrelax(call, [member(X, [1,2,3,4,5])], [X > 30, X > 2, X >= 4], R),
    R =@= [X>2, X>=4].

test(explain2) :-
    qrelax(call, [X in 1..3], [X #> 30, X#>2, X#>=4], R),
    R =@= [X #> 2].

test(explain3) :-
    qexplain(call,[X in 1..5], [X=1, X=2, X>1], R),
    R =@= [X=1, X=2].

test(explain4) :-
    qexplain(call, [member(X,[1,2,3,4,5])], [X=1, X=2, X>1, X < 0], R),
    R =@= [X=1, X=2].

test(explain5) :-
    qexplain(call, [member(X,[1,2,3,4,5])], [X=1, X < 0, X=2, X>1], R),
    R =@= [X<0].

test(explain6) :-
    qexplain(call, [(X + Y) #>= 10], [X#<5, Y#<5, X#>2, X#>4], R),
    R =@= [X#<5, Y#<5].

test(topexplain1) :-
    top_explain(call, [(X + Y) #>= 10], [X#<5, Y#<5, X#>2, X#>4], R),
    R =@= [X#<5, Y#<5].

test(topexplain2, [true(R == "consistent")]) :-
    top_explain(call, [Y #> 0], [X#<5, Y#<5, X#>2], R).

test(toprelax, true(R == [(X #> 2), (X#>4), (Y#<5)])) :-
    top_relax(call, [(X + Y) #>= 10], [X#<5, Y#<5, X#>2, X#>4], R).

test(toprelax2, [true(R == "consistent")]) :-
    top_relax(call, [Y #> 0], [X#<5, Y#<5, X#>2], R).


:- end_tests(quickexplain_tests).
