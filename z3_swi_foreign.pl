%%% -*- Mode: Prolog; Module: z3; -*-

%% this is the lowest-level wrapper

:- module(z3_foreign, [

            z3_print_status/1,
            z3_declare/2,
            z3_push/2,
            z3_push/1

            ]).

:- load_foreign_library(z3_swi_foreign).

:- initialization(reset_globals).

reset_globals :- reset_global_solver, reset_var_counts, z3_reset_declarations.


%% TODO: move this to the next-level-up file:
%% should only be called at the top-most level:
reset_global_solver :-
    z3_mk_solver(S),
    nb_setval(global_solver, S),
    nb_setval(solver_depth, 0).

get_global_solver(S) :- nb_getval(global_solver, S). 

z3_print_status(Status) :- get_global_solver(Solver), z3_solver_check_and_print(Solver, Status).
 
reset_var_counts :- nb_setval(varcount, 0).
 
