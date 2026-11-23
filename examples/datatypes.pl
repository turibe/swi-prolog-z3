#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: datatype_examples; -*-

%% Examples of algebraic datatypes: records, lists, trees, options, and datatypes that refer to each
%% other. A datatype is declared by its constructors:
%%
%%     z3_declare_datatype(list, [nil, cons(head:int, tail:list)])
%%
%% which declares the constructors nil and cons/2, the recognizers is_nil/1 and is_cons/1, and the
%% accessors head/1 and tail/1. Z3 knows that values built by different constructors differ, that
%% constructors are injective (cons(A, B) = cons(C, D) only if A = C and B = D), and that values are
%% finite: no list is its own tail.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/datatypes.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/datatypes).
%%     ?- example(increasing_list).
%%     ?- run_tests(datatype_examples).

:- module(datatype_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').

:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

% Each example starts from a fresh solver, with these datatypes declared.
example(Name, Answer) :-
    question(Name, _),
    z3_reset,
    declare_datatypes,
    answer(Name, Answer).

example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(datatype_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

declare_datatypes :-
    z3_declare_datatype(list, [nil, cons(head:int, tail:list)]),
    z3_declare_datatype(tree, [leaf, node(left:tree, value:int, right:tree)]),
    z3_declare_datatype(point, [point(x:real, y:real)]),
    z3_declare_datatype(option, [none, some(get:int)]),
    % An expression can contain a block of statements, and a statement can contain expressions.
    z3_declare_datatypes([expr-[num(val:int), plus(a:expr, b:expr), block(body:stmt)],
                          stmt-[skip, seq(first:stmt, rest:stmt), print(e:expr)]]).

yes_no(Goal, Answer) :- ( call(Goal) -> Answer = yes ; Answer = no ).

question(increasing_list,
         "Find a list of three positive integers, increasing, that add up to 6.").
question(injective,
         "If cons(a, s) = cons(b, t), must a = b and s = t?").
question(no_cycles,
         "Can a list be its own tail? Can a tree be its own left subtree?").
question(tree_shape,
         "Find a tree with exactly two nodes, whose values add up to 10, with the bigger value at the root.").
question(rectangle,
         "Point p is (1.0, 2.0). Is it inside the rectangle from (0.0, 0.0) to (3.0, 3.0)?").
question(safe_division,
         "Dividing with an option: r is none when d = 0, and some(n div d) otherwise. With n = 7, what is r for d = 0 and for d = 2?").
question(mutual_recursion,
         "An expression holds a block of statements, which prints an expression. What is the number printed in block(seq(skip, print(num(42))))?").
question(smtlib2,
         "Export a list constraint as SMT-LIB2, and read it back: is the head still 5?").

% z3_label/1 asks Z3 for values, one solution per answer.
answer(increasing_list, L) :-
    z3_push(L = cons(A, cons(B, cons(C, nil)))),
    z3_push(A:int > 0 and A < B and B < C and A + B + C = 6),
    once(z3_label([L])).

answer(injective, Answer) :-
    yes_no(z3_is_implied(implies(cons(a:int, s:list) = cons(b:int, t:list), a = b and s = t)), Answer).

% Datatype values are finite terms, so Z3 does an occurs check, as Prolog unification would.
answer(no_cycles, [own_tail-Tail, own_left_subtree-Left]) :-
    yes_no(z3_is_consistent(is_cons(l:list) and tail(l) = l), Tail),
    yes_no(z3_is_consistent(is_node(t:tree) and left(t) = t), Left).

answer(tree_shape, T) :-
    z3_push(T = node(L, V, R)),
    z3_push(is_leaf(L:tree) and is_node(R:tree) and is_leaf(left(R)) and is_leaf(right(R))),
    z3_push(V:int + value(R) = 10 and V > value(R) and value(R) > 0),
    once(z3_label([T])).

answer(rectangle, Inside) :-
    z3_push(p:point = point(1.0, 2.0)),
    z3_push(lo:point = point(0.0, 0.0) and hi:point = point(3.0, 3.0)),
    yes_no(z3_is_implied(x(lo) =< x(p) and x(p) =< x(hi) and y(lo) =< y(p) and y(p) =< y(hi)), Inside).

answer(safe_division, [d0-R0, d2-R2]) :-
    division(0, R0),
    division(2, R2).

answer(mutual_recursion, N) :-
    z3_push(x:expr = block(seq(skip, print(num(42))))),
    z3_push(n:int = val(e(rest(body(x))))),
    z3_model(M),
    memberchk(n = N, M.constants).

% The SMT-LIB2 text declares the datatype; reading it back declares it again, after z3_reset/0.
answer(smtlib2, head_is_5-Answer) :-
    z3_push(l:list = cons(5, nil)),
    z3_smtlib2(S),
    z3_reset,
    z3_push_smtlib2(S),
    yes_no(z3_is_implied(head(l) = 5), Answer).

% Each division in its own findall/3, which undoes its pushes.
division(D, R) :-
    findall(R0, ( z3_push(n:int = 7 and d:int = D),
                  z3_push(r:option = ite(d = 0, none, some(n div d))),
                  z3_model(M),
                  memberchk(r = R0, M.constants) ),
            [R]).

:- begin_tests(datatype_examples).

expected(increasing_list, cons(1, cons(2, cons(3, nil)))).
expected(injective, yes).
expected(no_cycles, [own_tail-no, own_left_subtree-no]).
expected(rectangle, yes).
expected(safe_division, [d0-none, d2-some(3)]).
expected(mutual_recursion, 42).
expected(smtlib2, head_is_5-yes).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

test(tree_shape) :-
    example(tree_shape, T),
    T = node(leaf, V, node(leaf, W, leaf)),
    assertion(V + W =:= 10),
    assertion(V > W),
    assertion(W > 0).

:- end_tests(datatype_examples).
