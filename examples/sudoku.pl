#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: sudoku_examples; -*-

%% Sudoku with Z3. Each cell is a constant, c11 to c99 (row, then column), whose sort is digit, an
%% enumeration of the nine values d1 to d9; the rules say that each row, column and 3x3 box has nine
%% distinct digits. A puzzle adds one equation per clue. Z3 then solves it, and can do things that
%% are awkward with plain search: check that a solution is the only one, count solutions, and say
%% which clues of an impossible puzzle conflict.
%%
%% Why an enumeration, and not integers from 1 to 9? Z3 checks the formulas each time one is pushed,
%% and with integers, finding any grid for the rules alone, before the clues, takes it far too long:
%% even a grid with only distinct rows and columns (a Latin square) takes 20 seconds or more. With an
%% enumeration sort, a finite set of values, it takes a fraction of a second. examples/smt2/ has that
%% Latin square for the z3 command line, with integers, an enumeration and bit-vectors.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/sudoku.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/sudoku).
%%     ?- example(hardest).
%%     ?- run_tests(sudoku_examples).
%% or solve a puzzle of your own, given as nine strings, with . or 0 for an empty cell:
%%     ?- solve(["53..7....", "6..195...", ...], Rows).

:- module(sudoku_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2,          % example(?Name, -Answer): Answer is the example's result
              solve/2,            % solve(+Puzzle, -Rows): Rows is a solution of Puzzle
              print_grid/1        % print_grid(+Rows): prints a grid
          ]).

:- use_module('../z3').

% Run main only when this file is the script swipl was started with, not when it is loaded.
:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

%! example(?Name, -Answer) is nondet.
%  Answer is the result of the example Name, computed from a fresh solver.
example(Name, Answer) :-
    question(Name, _),
    z3_reset,
    answer(Name, Answer).

%! example(?Name) is nondet.
%  Runs the example Name, printing its question and answer.
example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n", [Question]),
    print_answer(Answer),
    nl.

print_answer(grid(Rows)) :- !, print_grid(Rows).
print_answer(Answer) :- format("  ~q~n", [Answer]).

main :- forall(question(Name, _), example(Name)).

% ------------------------------------------------------------------------------------------------
% The rules, and the clues of a puzzle.

index(I) :- between(1, 9, I).

% The constant for the cell at row R and column C, such as c19 for row 1, column 9. (Constants are
% much faster for Z3 than an uninterpreted function cell(R, C) would be.) Works both ways.
cell(R, C, Cell) :-
    (   atom(Cell)
    ->  atom_chars(Cell, [c, RC, CC]), atom_number(RC, R), atom_number(CC, C)
    ;   format(atom(Cell), "c~w~w", [R, C])
    ).

% z3_push/1 is undone on backtracking, like any Prolog binding, so formulas are collected first and
% then pushed, with maplist/2 or as one formula, not pushed inside forall/2 or a failure-driven loop.

% The digit D, from 1 to 9, is the value Value of the enumeration sort digit, from d1 to d9.
digit_value(D, Value) :-
    (   atom(Value)
    ->  atom_concat(d, A, Value), atom_number(A, D)
    ;   atom_concat(d, D, Value)
    ).

% Enumeration sorts are not undone on backtracking, and z3_reset/0 forgets them, so each example
% declares digit again after its reset.
declare_digits :-
    findall(V, ( index(D), digit_value(D, V) ), Values),
    z3_declare_enum(digit, Values).

% Each row, column and box is a group of nine cells that must all differ.
group(row(R), Cells) :- index(R), findall(Cell, ( index(C), cell(R, C, Cell) ), Cells).
group(column(C), Cells) :- index(C), findall(Cell, ( index(R), cell(R, C, Cell) ), Cells).
group(box(BR, BC), Cells) :-
    member(BR, [1, 4, 7]), member(BC, [1, 4, 7]),
    findall(Cell, ( between(0, 2, I), between(0, 2, J), R is BR + I, C is BC + J, cell(R, C, Cell) ),
            Cells).

% Every cell is given its sort, digit, where it first appears.
distinct_cells(Cells, Distinct) :-
    findall(Cell:digit, member(Cell, Cells), Typed),
    Distinct =.. [distinct | Typed].

distinct_cells(Cells) :-
    distinct_cells(Cells, Distinct),
    z3_push(Distinct).

push_rules :-
    declare_digits,
    push_groups.

% The rules are pushed as one formula, a conjunction, so Z3 checks them once, not 27 times.
push_groups :- push_groups(l_true).

push_groups(Status) :-
    findall(Distinct, ( group(_, Cells), distinct_cells(Cells, Distinct) ), Rules),
    conjunction(Rules, All),
    z3_push(All, Status).

%! push_puzzle(+Puzzle) is semidet.
%  Pushes the rules and the clues of Puzzle. Fails if it has no solution.
%  The clues go first: Z3 checks the formulas at each push, and finding a grid for the rules alone,
%  with no clues, takes it about a second, against a tenth of a second for the rules after the clues.
push_puzzle(Puzzle) :-
    declare_digits,
    clues(Puzzle, Clues),
    maplist(z3_push, Clues),
    push_groups.

conjunction([F], F) :- !.
conjunction([F | Fs], F and G) :- conjunction(Fs, G).

%! clues(+Puzzle, -Clues) is det.
%  Clues are the equations Cell = Value, such as c19 = d9, for the filled cells of Puzzle, nine
%  strings of nine characters with a digit, or . or 0 for an empty cell.
clues(Puzzle, Clues) :-
    findall(Cell = Value,
            ( nth1(R, Puzzle, Row), string_chars(Row, Chars), nth1(C, Chars, Char),
              char_type(Char, digit(D)), D > 0, cell(R, C, Cell), digit_value(D, Value) ),
            Clues).

% The grid in a model of the formulas pushed, as nine lists of nine digits. Evaluating the list of
% all the cells at once reads them from one model.
model_rows(Rows) :-
    findall(Cell, ( index(R), index(C), cell(R, C, Cell) ), Cells),
    z3_eval(Cells, true, Values),
    maplist(digit_value, Digits, Values),
    rows(Digits, Rows).

rows([], []).
rows([D | Ds], [Row | Rows]) :- length(Row, 9), append(Row, Rest, [D | Ds]), rows(Rest, Rows).

% A clue, as cell(Row, Column) = Digit.
clue_cell(Cell = Value, cell(R, C) = D) :- cell(R, C, Cell), digit_value(D, Value).

% The formula that says the grid differs from Rows somewhere.
different_from(Rows, Different) :-
    findall(Cell <> Value,
            ( nth1(R, Rows, Row), nth1(C, Row, D), cell(R, C, Cell), digit_value(D, Value) ),
            Differences),
    Different =.. [or | Differences].

%! solve(+Puzzle, -Rows) is semidet.
%  Rows is a solution of Puzzle. Fails if it has none.
solve(Puzzle, Rows) :-
    push_puzzle(Puzzle),
    model_rows(Rows).

%! count_solutions(+Puzzle, +Limit, -Count) is det.
%  Count is the number of solutions of Puzzle, if there are at most Limit; more(Limit) otherwise.
%  Each solution found is ruled out, and Z3 is asked for another, until there are none left.
%  (z3_push/2 gives the status, where z3_push/1 would fail once no solution is left.)
count_solutions(Puzzle, Limit, Count) :-
    (   solve(Puzzle, Rows)
    ->  count_more(Rows, 1, Limit, Count)
    ;   Count = 0
    ).

% Rows is the solution number N.
count_more(Rows, N, Limit, Count) :-
    different_from(Rows, Different),
    z3_push(Different, Status),
    (   Status \== l_true
    ->  Count = N
    ;   N >= Limit
    ->  Count = more(Limit)
    ;   model_rows(Next),
        N1 is N + 1,
        count_more(Next, N1, Limit, Count)
    ).

%! print_grid(+Rows) is det.
%  Prints a grid of nine rows, with lines between the boxes.
print_grid(Rows) :-
    forall(nth1(R, Rows, Row),
           (   ( R =:= 4 ; R =:= 7 ) -> format("  ------+-------+------~n"), print_row(Row)
           ;   print_row(Row)
           )).

print_row([A, B, C, D, E, F, G, H, I]) :-
    maplist(digit_char, [A, B, C, D, E, F, G, H, I], Cs),
    format("  ~w ~w ~w | ~w ~w ~w | ~w ~w ~w~n", Cs).

digit_char(D, '.') :- D == 0, !.
digit_char(D, D).

% ------------------------------------------------------------------------------------------------
% The puzzles.

% Called "the world's hardest sudoku" by its author, Arto Inkala, in 2012.
puzzle(hardest, ["8........",
                 "..36.....",
                 ".7..9.2..",
                 ".5...7...",
                 "....457..",
                 "...1...3.",
                 "..1....68",
                 "..85...1.",
                 ".9....4.."]).

% A classic one, from the Wikipedia article on sudoku.
puzzle(classic, ["53..7....",
                 "6..195...",
                 ".98....6.",
                 "8...6...3",
                 "4..8.3..1",
                 "7...2...6",
                 ".6....28.",
                 "...419..5",
                 "....8..79"]).

% The classic puzzle with its first row emptied: too few clues to fix the answer.
puzzle(few_clues, [".........",
                   "6..195...",
                   ".98....6.",
                   "8...6...3",
                   "4..8.3..1",
                   "7...2...6",
                   ".6....28.",
                   "...419..5",
                   "....8..79"]).

% The classic puzzle with an 8 added in the first row, in column 7. No two clues clash, as no row,
% column or box repeats a digit, yet the puzzle has no solution.
puzzle(impossible, ["53..7.8..",
                    "6..195...",
                    ".98....6.",
                    "8...6...3",
                    "4..8.3..1",
                    "7...2...6",
                    ".6....28.",
                    "...419..5",
                    "....8..79"]).

% ------------------------------------------------------------------------------------------------
% The examples: a question, in words, and the code that answers it.

question(classic,
         "Solve the sudoku from the Wikipedia article.").
question(hardest,
         "Solve \"the world's hardest sudoku\" (Arto Inkala, 2012).").
question(unique,
         "Is that the only solution of the hardest sudoku?").
question(few_clues,
         "Empty the first row of the classic puzzle. How many solutions are there now?").
question(impossible,
         "Add an 8 in row 1, column 7 of the classic puzzle. No row, column or box repeats a digit, but there is no solution. Which clues conflict?").
question(diagonals,
         "Fill an empty grid so that both diagonals, too, have nine different digits.").

answer(classic, grid(Rows)) :-
    puzzle(classic, Puzzle),
    solve(Puzzle, Rows).

answer(hardest, grid(Rows)) :-
    puzzle(hardest, Puzzle),
    solve(Puzzle, Rows).

% Find the solution, rule it out, and check that nothing is left.
answer(unique, Answer) :-
    puzzle(hardest, Puzzle),
    solve(Puzzle, Rows),
    different_from(Rows, Different),
    (   z3_is_consistent(Different) -> Answer = no ; Answer = yes ).

answer(few_clues, Count) :-
    puzzle(few_clues, Puzzle),
    count_solutions(Puzzle, 100, Count).

% The rules are pushed first, so z3_explain/2 looks for a minimal set of clues that, with the
% rules, cannot all hold: removing any one of them would leave a puzzle with a solution. The answer
% gives each clue as cell(Row, Column) = Digit.
answer(impossible, Conflicting) :-
    puzzle(impossible, Puzzle),
    push_rules,
    clues(Puzzle, Clues),
    z3_explain(Clues, Core),
    maplist(clue_cell, Core, Conflicting).

% A variant is one more rule: here, two more groups.
answer(diagonals, grid(Rows)) :-
    push_rules,
    findall(Cell, ( index(I), cell(I, I, Cell) ), Down),
    findall(Cell, ( index(I), C is 10 - I, cell(I, C, Cell) ), Up),
    distinct_cells(Down),
    distinct_cells(Up),
    model_rows(Rows).

% ------------------------------------------------------------------------------------------------

:- begin_tests(sudoku_examples).

% Rows is a full grid that follows the rules, and agrees with the clues of Puzzle.
valid(Rows, Puzzle) :-
    length(Rows, 9),
    forall(member(Row, Rows), ( length(Row, 9), forall(member(D, Row), between(1, 9, D)) )),
    forall(group(_, Cells),
           ( findall(D, ( member(Cell, Cells), cell(R, C, Cell), nth1(R, Rows, Row), nth1(C, Row, D) ), Ds),
             sort(Ds, Sorted), length(Sorted, 9) )),
    clues(Puzzle, Clues),
    forall(member(Cell = Value, Clues),
           ( cell(R, C, Cell), digit_value(D, Value), nth1(R, Rows, Row), nth1(C, Row, D) )).

test(classic) :-
    example(classic, grid(Rows)),
    puzzle(classic, Puzzle),
    assertion(valid(Rows, Puzzle)),
    assertion(Rows = [[5,3,4,6,7,8,9,1,2] | _]).

test(hardest) :-
    example(hardest, grid(Rows)),
    puzzle(hardest, Puzzle),
    assertion(valid(Rows, Puzzle)),
    assertion(Rows == [[8,1,2,7,5,3,6,4,9], [9,4,3,6,8,2,1,7,5], [6,7,5,4,9,1,2,8,3],
                       [1,5,4,2,3,7,8,9,6], [3,6,9,8,4,5,7,2,1], [2,8,7,1,6,9,5,3,4],
                       [5,2,1,9,7,4,3,6,8], [4,3,8,5,2,6,9,1,7], [7,9,6,3,1,8,4,5,2]]).

test(unique) :-
    example(unique, Answer),
    assertion(Answer == yes).

test(few_clues) :-
    example(few_clues, Count),
    assertion(Count == 2).

test(impossible) :-
    example(impossible, Conflicting),
    assertion(memberchk(cell(1, 7) = 8, Conflicting)),
    % The answer is really inconsistent with the rules, and minimal: dropping any clue fixes it.
    maplist(clue_cell, Clues, Conflicting),
    assertion(\+ consistent(Clues)),
    forall(select(_, Clues, Rest), assertion(consistent(Rest))).

consistent(Clues) :-
    z3_reset,
    declare_digits,
    maplist(z3_push, Clues),
    push_groups(Status),
    Status == l_true.

test(diagonals) :-
    example(diagonals, grid(Rows)),
    assertion(valid(Rows, [])),
    findall(D, ( index(I), nth1(I, Rows, Row), nth1(I, Row, D) ), Down),
    findall(D, ( index(I), nth1(I, Rows, Row), C is 10 - I, nth1(C, Row, D) ), Up),
    assertion(( sort(Down, S1), length(S1, 9) )),
    assertion(( sort(Up, S2), length(S2, 9) )).

:- end_tests(sudoku_examples).
