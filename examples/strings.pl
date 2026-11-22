#!/usr/bin/env -S swipl -q
%%% -*- Mode: Prolog; Module: string_examples; -*-

%% Examples of string constraints. Strings have the sort string, and operations named str_...:
%% str_concat, str_len, str_substr(S, Offset, Length), str_at(S, I), str_contains(S, Part),
%% str_prefixof(Prefix, S), str_suffixof(Suffix, S), str_indexof(S, Part, Start), str_replace,
%% str_lt and str_le (lexicographic), str_to_int and int_to_str. Z3 can solve for strings, not just
%% check them: give it constraints, and a model gives strings that meet them.
%%
%% Run it as a script, to print each question and answer:
%%     ./examples/strings.pl
%% or load it and run one example, or the tests:
%%     ?- use_module(examples/strings).
%%     ?- example(password).
%%     ?- run_tests(string_examples).

:- module(string_examples, [
              example/1,          % example(?Name): runs the example called Name, printing it
              example/2           % example(?Name, -Answer): Answer is the example's result
          ]).

:- use_module('../z3').

:- prolog_load_context(source, This),
   (   current_prolog_flag(associated_file, This)
   ->  initialization(main, main)
   ;   true
   ).

example(Name, Answer) :- question(Name, _), z3_reset, answer(Name, Answer).

example(Name) :-
    question(Name, Question),
    example(Name, Answer),
    format("~w~n  ~W~n~n", [Question, Answer, [module(string_examples), quoted(true)]]).

main :- forall(question(Name, _), example(Name)).

value(Name, Value) :- z3_model(M), memberchk(Name = Value, M.constants).

question(password,
         "Find a password of 8 characters that starts with Z, ends with !, contains a 7, and has no spaces.").
question(word_equation,
         "Which 4-character string x makes x ++ \"ab\" equal to \"ab\" ++ x?").
question(split_email,
         "Split alice@example.com into the user and the domain, at the @.").
question(digits,
         "Find a 3-digit number over 900 whose middle digit is 5, as a string.").
question(unicode,
         "How long is the string \"héllo ✓\"? (Strings are sequences of Unicode characters.)").
question(order,
         "Is \"apple\" before \"banana\", and \"Zebra\" before \"apple\", in lexicographic order?").

answer(password, P) :-
    z3_push(str_len(p:string) = 8),
    z3_push(str_prefixof("Z", p)),
    z3_push(str_suffixof("!", p)),
    z3_push(str_contains(p, "7")),
    z3_push(not(str_contains(p, " "))),
    value(p, P).

% A word equation: x ++ "ab" = "ab" ++ x holds when x is "ab" repeated.
answer(word_equation, X) :-
    z3_push(str_concat(x:string, "ab") = str_concat("ab", x)),
    z3_push(str_len(x) = 4),
    value(x, X).

answer(split_email, user(User)-domain(Domain)) :-
    z3_push(e:string = "alice@example.com"),
    z3_push(i:int = str_indexof(e, "@", 0)),
    z3_push(user:string = str_substr(e, 0, i)),
    z3_push(domain:string = str_substr(e, i + 1, str_len(e) - i - 1)),
    value(user, User),
    value(domain, Domain).

% str_to_int gives the number a string of digits stands for (or -1 if it is not one).
answer(digits, S) :-
    z3_push(n:int = str_to_int(s:string)),
    z3_push(str_len(s) = 3),
    z3_push(n > 900),
    z3_push(str_at(s, 1) = "5"),
    value(s, S).

answer(unicode, N) :-
    z3_push(n:int = str_len("héllo ✓")),
    value(n, N).

% Lexicographic order compares character codes, so capital letters come before small ones.
answer(order, [apple_before_banana-A, zebra_before_apple-B]) :-
    ( z3_is_implied(str_lt("apple", "banana")) -> A = yes ; A = no ),
    ( z3_is_implied(str_lt("Zebra", "apple")) -> B = yes ; B = no ).

:- begin_tests(string_examples).

expected(word_equation, "abab").
expected(split_email, user("alice")-domain("example.com")).
expected(unicode, 7).
expected(order, [apple_before_banana-yes, zebra_before_apple-yes]).

test(answers, [forall(expected(Name, Expected))]) :-
    example(Name, Answer),
    assertion(Answer == Expected).

% The password and the number can be any that meet the constraints; check that they do.
test(password) :-
    example(password, P),
    assertion(string_length(P, 8)),
    assertion(sub_string(P, 0, 1, _, "Z")),
    assertion(sub_string(P, _, 1, 0, "!")),
    assertion(sub_string(P, _, _, _, "7")),
    assertion(\+ sub_string(P, _, _, _, " ")).

test(digits) :-
    example(digits, S),
    number_string(N, S),
    assertion((N > 900, N < 1000)),
    assertion(sub_string(S, 1, 1, _, "5")).

:- end_tests(string_examples).
