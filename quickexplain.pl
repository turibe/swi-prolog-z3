%%% -*- Mode: Prolog; Module: quickexplain; -*-

:- module(quickexplain, [
              % These assume that Base+Constraints is unsatisfiable:
              qexplain/4, % +AssertPredicate, +Base, +Constraints, -Result
              qexplain/3, % +AssertPredicate, +Constraints, -Result   (empty Base)
              
              qrelax/4,   % +AssertPredicate, +Base, +Constraints, -Result
              qrelax/3,   % +AssertPredicate, +Constraints, -Result   (empty Base)

              % Use these if you want a consistency check at the start:
              check_explain/4,   % +AssertPredicate, +Base, +Constraints, -Result
              check_explain/3,   % +AssertPredicate, +Constraints, -Result   (empty Base)

              check_relax/4,   % +AssertPredicate, +Base, +Constraints, -Result
              check_relax/3    % +AssertPredicate, +Constraints, -Result   (empty Base)

          ]).

/** <module> Quickexplain

SWI Prolog implementation of Ulrich Junker's Quickxplain (https://cdn.aaai.org/AAAI/2004/AAAI04-027.pdf),
for finding minimally unsatisfiable subsets, and maximally satisfiable ones.

Each predicate takes Assert, a predicate that adds one constraint: Assert(C) succeeds if C can be
added consistently to the constraints added so far, and fails if not. Its effects must be undone on
backtracking, as for CLP constraints (call/1) or z3.pl's z3_push/1, since constraint sets are tried
inside \+ \+. Assert should fail only on inconsistency: a failure for another reason, such as a type
error, is taken for a conflict (z3.pl's z3_explain/2 and z3_relax/2 avoid this for Z3 formulas).

Base is a list of constraints that always hold; it is added first in each check.

@author Tomas Uribe
@license MIT
*/

:- meta_predicate qexplain(1, ?, ?).
:- meta_predicate qexplain(1, ?, ?, ?).
:- meta_predicate qrelax(1, ?, ?).
:- meta_predicate qrelax(1, ?, ?, ?).

:- meta_predicate check_explain(1, ?, ?).
:- meta_predicate check_explain(1, ?, ?, ?).
:- meta_predicate check_relax(1, ?, ?).
:- meta_predicate check_relax(1, ?, ?, ?).

:- use_module(utils).

% debuginfo(X) :- writeln(X), flush_output.
% debuginfo(X, Y) :- write(X), writeln(Y), flush_output.
debuginfo(_X) :- true.
debuginfo(_X, _Y) :- true.

%% Both explain and relax assume that Base + Constraints are, together, inconsistent;
%% if they are not, Output = Constraints, which is fine for relax but confusing for explain.
%% use the "check_" procedures to check consistency first.

%! qexplain(:Assert, +Base, +Constraints, -Result) is det.
%  Assuming Base + Constraints is unsat, Result is a minimal subset of Constraints, in their order, that
%  is unsat with Base: removing any constraint from it makes it consistent. Of several such subsets, it
%  is the one whose last constraint comes earliest. Result is [] if Base is unsat by itself; if Base +
%  Constraints is consistent, Result is all of Constraints (check_explain/4 checks first).
qexplain(_Assert, _Base, [], Output) :- !, Output = [].
qexplain(Assert, Base, Constraints, Output) :-
    rec_qexplain(Assert, Base, Base, Constraints, Output).

%! qexplain(:Assert, +Constraints, -Result) is det.
%  qexplain/4 with an empty Base.
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

%! check_explain(:Assert, +Base, +Constraints, -Result) is det.
%  Checks whether Base + Constraints is unsat. If so, Result is as for qexplain/4; otherwise, Result is
%  `consistent`.
check_explain(Assert, Base, Constraints, Output) :-
    consistent(Assert, Base, Constraints) -> Output = consistent; qexplain(Assert, Base, Constraints, Output).

%! check_explain(:Assert, +Constraints, -Result) is det.
%  check_explain/4 with an empty Base.
check_explain(Assert, Constraints, Output) :- check_explain(Assert, [], Constraints, Output).

%! qrelax(:Assert, +Base, +Constraints, -Result) is det.
%  Result is a maximal subset of Constraints that is consistent with Base: adding any other constraint
%  makes it inconsistent. When constraints conflict, later ones are kept over earlier ones. Result is
%  not in the order of Constraints. If Base + Constraints is consistent, Result is Constraints; if
%  Base is inconsistent by itself, it is [].
qrelax(_Assert, _B, [], Result) :- !, Result = [].
qrelax(Assert, B, Constraints, Result) :-
    rec_qrelax(Assert, B, Constraints, Result).

%! qrelax(:Assert, +Constraints, -Result) is det.
%  qrelax/4 with an empty Base.
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

%! check_relax(:Assert, +Base, +Constraints, -Result) is det.
%  Checks whether Base + Constraints is consistent. If so, Result is `consistent`; otherwise, it is as
%  for qrelax/4.
check_relax(Assert, Base, Constraints, Output) :-
    consistent(Assert, Base, Constraints) -> Output = consistent; qrelax(Assert, Base, Constraints, Output).

%! check_relax(:Assert, +Constraints, -Result) is det.
%  check_relax/4 with an empty Base.
check_relax(Assert, Constraints, Output) :- check_relax(Assert, [], Constraints, Output).

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

test(check_explain1) :-
    check_explain(call, [(X + Y) #>= 10], [X#<5, Y#<5, X#>2, X#>4], R),
    R =@= [X#<5, Y#<5].

test(check_explain2, [true(R == consistent)]) :-
    check_explain(call, [Y #> 0], [X#<5, Y#<5, X#>2], R).

test(check_relax, true(R == [(X #> 2), (X#>4), (Y#<5)])) :-
    check_relax(call, [(X + Y) #>= 10], [X#<5, Y#<5, X#>2, X#>4], R).

test(check_relax2, [true(R == consistent)]) :-
    check_relax(call, [Y #> 0], [X#<5, Y#<5, X#>2], R).

% Edge cases.

test(explain_empty, [true(R == [])]) :-
    qexplain(call, [], R).

test(relax_empty, [true(R == [])]) :-
    qrelax(call, [], R).

test(explain_single, [true(R == [fail])]) :-
    qexplain(call, [fail], R).

test(relax_single, [true(R == [])]) :-
    qrelax(call, [fail], R).

% An inconsistent base needs none of the constraints.
test(explain_base_inconsistent, [true(R == [])]) :-
    qexplain(call, [fail], [true, X = 1, X = 2], R).

test(relax_base_inconsistent, [true(R == [])]) :-
    qrelax(call, [fail], [true, true], R).

% qexplain assumes Base + Constraints are inconsistent; if not, it returns all the Constraints
% (check_explain/3 checks first).
test(explain_consistent_returns_all, [true(R == [true, true])]) :-
    qexplain(call, [true, true], R).

% With two separate conflicts, one is reported: the one whose last constraint comes first.
test(explain_two_conflicts, [true(R =@= [X = 1, X = 2])]) :-
    qexplain(call, [X = 1, Y = 1, X = 2, Y = 2], R).

% When constraints conflict, qrelax keeps the later ones.
test(relax_keeps_later, [true(R =@= [X = 2])]) :-
    qrelax(call, [X = 1, X = 2], R).

% Randomized checks against the definitions. The constraints are unary CLP(FD) constraints on one
% variable, for which propagation decides consistency exactly. For each random set:
%   qexplain: the result is inconsistent with the base, and removing any constraint makes it consistent;
%   qrelax: the result is consistent with the base, and adding any other constraint makes it inconsistent.

random_constraint(X, C) :-
    random_between(0, 9, K),
    random_member(Op, [#>=, #=<, #\=, #=]),
    C =.. [Op, X, K].

random_problem(Base, Constraints) :-
    random_between(1, 8, N),
    length(Constraints, N),
    Base = [X in 0..9],
    maplist(random_constraint(X), Constraints).

holds(Cs) :- \+ \+ maplist(call, Cs).

minimal_conflict(Base, Core) :-
    \+ holds_all(Base, Core),
    forall(select(_, Core, Rest), holds_all(Base, Rest)).

maximal_consistent(Base, Constraints, Kept) :-
    holds_all(Base, Kept),
    forall(( member(C, Constraints), \+ (member(K, Kept), K == C) ),
           \+ holds_all(Base, [C|Kept])).

holds_all(Base, Cs) :- append(Base, Cs, All), holds(All).

subset_eq(Sub, Set) :- forall(member(S, Sub), (member(T, Set), T == S)).

test(random_explain_minimal, [setup(set_random(seed(1)))]) :-
    forall(between(1, 300, _),
           (   random_problem(Base, Cs),
               (   holds_all(Base, Cs)
               ->  true
               ;   qexplain(call, Base, Cs, R),
                   assertion(subset_eq(R, Cs)),
                   assertion(minimal_conflict(Base, R))
               )
           )).

test(random_relax_maximal, [setup(set_random(seed(2)))]) :-
    forall(between(1, 300, _),
           (   random_problem(Base, Cs),
               qrelax(call, Base, Cs, R),
               assertion(subset_eq(R, Cs)),
               assertion(maximal_consistent(Base, Cs, R))
           )).


:- end_tests(quickexplain_tests).
