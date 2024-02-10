
#include <stdio.h>
#include <SWI-Prolog.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include <z3.h>

/****

     This is a C foreign interface between SWI Prolog and the Z3 prover. It exposes the basic Z3 functionality
     as Prolog predicates, leaving the implementation of more complex applications to Prolog code and libraries.

     The main decision is how to handle state -- context, declarations and solvers.

     It would be nice to embed the declarations in the context object, but this does not seem to be possible.
     We then keep a map of signatures (name, arity, type) to declarations.
     (We assume for now that functions are not overloaded by type or arity.)

     For now, we go with one global, implicit context object, and one global declaration map;
     everything else, including solvers, is created and destroyed at the Prolog level.
     
     A more functional approach would get rid of the global vars, and pass them as arguments.
     
*****/

/***** Guide to types:

      atom_t    SWI type, Prolog atom
      term_t    SWI type, Prolog term

*****/



// #define DEBUG(...) do {fprintf(stderr, "DEBUG: "); fprintf(stderr, __VA_ARGS__) ; fflush(stderr); } while (false)
#define DEBUG(...) {}
#define INPROGRESS(...) do {fprintf(stderr, "INPROGRESS: "); fprintf(stderr, __VA_ARGS__); fflush(stderr);} while (false)
#define ERROR(...) do {fprintf(stderr, "ERROR: "); fprintf(stderr, __VA_ARGS__); fflush(stderr);} while (false)
#define INFO(...) do {fprintf(stderr, "INFO: "); fprintf(stderr, __VA_ARGS__); fflush(stderr);} while (false)

// To raise Prolog errors, we could use PL_raise_exception, but the _ex functions are recommended instead.

// *************************************************************************


// from Z3's test_capi.c:
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol s = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}


Z3_ast mk_int_var(Z3_context ctx, const char * name) {
  Z3_sort ty = Z3_mk_int_sort(ctx);
  return mk_var(ctx, name, ty);
}

// we use intvars called "name/arity" as keys ; could have any other sort or shape...
// TODO: avoid sprintf by using a term "internalfn(name, arity)" as the key?

Z3_ast mk_ast_key(Z3_context ctx, const char * name, const size_t arity)
{
  char keyname[100]; // "name/arity" must fit in here.
  sprintf(keyname, "%s/%lu", name, arity);
  // INFO("key is %s\n", keyname);
  return mk_int_var(ctx, keyname);
}


/**
   \brief Check whether the logical context is satisfiable.
   If the context is satisfiable, then display the model.
*/

Z3_lbool solver_check_and_print(Z3_context ctx, Z3_solver s)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) {
          Z3_model_inc_ref(ctx, m);
          printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        }
        break;
    case Z3_L_TRUE:
        m = Z3_solver_get_model(ctx, s);
        if (m) {
          Z3_model_inc_ref(ctx, m);
          printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        }
        break;
    }
    if (m) {
      Z3_model_dec_ref(ctx, m);
    }
    return result; // this is the internal function
}

// ***************************** GLOBAL VARIABLES ********************************************


// For now, there is only one, global Z3 context object, implicit in most operations.
// Solver and model objects are explicit, and we can do push and pop on solvers from Prolog.

Z3_context global_z3_context = NULL;
long global_symbol_count = 0;
// Keeps around the declarations; not affected by push and pop:
Z3_ast_map global_declaration_map = NULL;


Z3_ast term_to_ast(Z3_context ctx, term_t formula);
foreign_t z3_ast_to_term_foreign(term_t ast_term, term_t formula);
foreign_t z3_ast_to_term_internal(Z3_ast ast, term_t formula);
Z3_sort mk_sort(Z3_context ctx, term_t formula);
Z3_symbol mk_symbol(Z3_context ctx, term_t formula);


void z3_swi_error_handler(Z3_context ctx, Z3_error_code e) {
  Z3_string msg = Z3_get_error_msg(ctx, e);
  fprintf(stderr, "Z3 ERROR: code %ul %s\n", e, msg);
}

void z3_swi_initialize() {
  Z3_string version = Z3_get_full_version();
  fprintf(stderr, "Using Z3 version %s\n", version);
  fprintf(stderr, "Initializing global context and declaration map\n");
  Z3_config config = Z3_mk_config();
  global_symbol_count = 0;
  global_z3_context = Z3_mk_context(config);
  global_declaration_map = Z3_mk_ast_map(global_z3_context);
  Z3_ast_map_inc_ref(global_z3_context, global_declaration_map);
  Z3_set_error_handler(global_z3_context, z3_swi_error_handler);
  Z3_del_config(config);
}


Z3_context get_context() { return global_z3_context; }

// ************************* END GLOBALS *************************


foreign_t z3_declaration_map_size_foreign(term_t result_term) {
  Z3_context ctx = get_context();
  int map_size = Z3_ast_map_size(ctx, global_declaration_map);
  return PL_unify_int64(result_term, map_size);
}

foreign_t z3_reset_declarations_foreign() {
  Z3_context ctx = get_context();
  Z3_ast_map_reset(ctx, global_declaration_map);
  global_symbol_count = 0;
  DEBUG("Cleared Z3 package global declaration map\n");
  return TRUE;
}

// We need function declarations to make terms.

Z3_func_decl get_function_declaration(Z3_context ctx, const char *name_string, const size_t arity) {
  assert(global_declaration_map != NULL);
  int map_size = Z3_ast_map_size(ctx, global_declaration_map);
  DEBUG("current map size is %d\n", map_size);
  Z3_ast key = mk_ast_key(ctx, name_string, arity);
  DEBUG("made key %s\n", Z3_ast_to_string(ctx, key));
  if (!Z3_ast_map_contains(ctx, global_declaration_map, key)) {
    DEBUG("key %s not in map\n", name_string);
    return NULL;
  }
  DEBUG("key %s is in map\n", name_string);
  Z3_ast value = Z3_ast_map_find(ctx, global_declaration_map, key);
  DEBUG("called map find\n");
  Z3_func_decl declaration = (Z3_func_decl) value;
  if (declaration != NULL) {
    // Z3_string rstring = Z3_ast_to_string(ctx, Z3_func_decl_to_ast(ctx, declaration));
    // DEBUG("Found declaration for %s: %s\n", name_string, rstring);
  }
  else {
    ERROR("Did not find declaration for %s\n", name_string);
    return NULL;
  }
  return declaration;
}


void register_function_declaration_string(Z3_context ctx, const char *name_string, const size_t arity, Z3_func_decl declaration) {
  Z3_ast key = mk_ast_key(ctx, name_string, arity);
  Z3_string rstring = Z3_ast_to_string(ctx, Z3_func_decl_to_ast(ctx, declaration));
  DEBUG("Installing declaration for %s: %s/%lu\n", name_string, rstring, arity);
  // the insert replaces any previous one.
  Z3_ast_map_insert(ctx, global_declaration_map, key, (Z3_ast) declaration);
  int size = Z3_ast_map_size(ctx, global_declaration_map);
  DEBUG("Declaration map has size %d\n", size);
}

/****
     for debugging; gets the declarations string into result:
***/
foreign_t z3_declarations_string_foreign(term_t result) {
  Z3_context ctx = get_context();
  Z3_string rstring =  Z3_ast_map_to_string(ctx, global_declaration_map);
  return PL_unify_string_chars(result, rstring);
}


// Question: how to garbage collect the context?

/*
 * Unifies the global context with the arg. Wraps in "context(X)".
 * Eventually should use blob mechanism to represent all pointers.
 */
foreign_t z3_context_foreign(term_t u) {
  Z3_context ctx = get_context();
  functor_t CONTEXT_FUNCTOR = PL_new_functor(PL_new_atom("context"), 1);
  term_t t  = PL_new_term_ref();
  term_t pt = PL_new_term_ref();
  int res = PL_unify_pointer(pt, ctx);
  if (!res) {
    ERROR("PL_unify_pointer failed getting context");
    return FALSE;
  }
  res = PL_cons_functor(t, CONTEXT_FUNCTOR, pt);
  if (!res) {
    ERROR("error calling PL_cons_functor");
    return FALSE;
  }

  return PL_unify(u, t);
}

/*
  makes a new solver and unifies it with the arg:
*/
foreign_t z3_mk_solver_foreign(term_t u) {
  int rval;
  Z3_context ctx = get_context();
  Z3_solver solver = Z3_mk_solver(ctx);
  DEBUG( "made solver %p\n", (void *) solver );
  Z3_solver_inc_ref(ctx, solver); // should be freed with z3_free_solver
  return PL_unify_pointer(u, solver);
}


/**
   Frees the solver, which must be an instantiated solver object.
   TODO: use setup_call_cleanup to do this automatically.
**/
foreign_t z3_free_solver_foreign(term_t u) {
  Z3_solver solver;
  Z3_context ctx  = get_context();
  int rval = PL_get_pointer_ex(u, (void **) &solver);
  if (!rval) {
    return rval;
  }
  DEBUG("freeing solver %p\n", (void *) solver);
  Z3_solver_dec_ref(ctx, solver);
  return rval;
}

foreign_t z3_free_model_foreign(term_t u) {
  Z3_model model;
  Z3_context ctx  = get_context();
  int rval = PL_get_pointer_ex(u, (void **) &model);
  if (!rval) {
    return rval;
  }
  DEBUG("freeing model %p\n", (void *) model);
  Z3_model_dec_ref(ctx, model);
  return rval;
}

/*
  Gets a model object from the solver; need to run check on the solver first.
  Otherwise, an error is reported and we fail.
*/

foreign_t z3_solver_get_model_foreign(term_t solver_term, term_t model_term) {
  Z3_solver solver;
  int rval = PL_get_pointer_ex(solver_term, (void **) &solver);
  if (!rval) return rval;
  Z3_context ctx  = get_context();
  Z3_model model = Z3_solver_get_model(ctx, solver);
  if (model) {
    Z3_model_inc_ref(ctx, model);
    return PL_unify_pointer(model_term, model);
  }
  return FALSE;
}

// TODO: model completion could be a flag
// In Prolog, we handle z3_push(X=14), z3_push(Y=X-5) by using attributed variables.
// TODO: handle z3_push(X=14), z3_push(Y=X-5), z3_model_eval(X*Y,R) by looking at attributed variables.
// need a higher-level model_eval that replaces vars by their attributes.
foreign_t z3_model_eval_foreign(term_t model_term, term_t term, term_t result_term) {
  Z3_model model;
  int rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) return rval;
  Z3_context ctx = get_context();
  Z3_ast to_eval = term_to_ast(ctx, term);
  if (to_eval == NULL) {
    return FALSE; // TODO: could return a status atom explaining what happened...
  }
  Z3_ast result_ast;
  bool result = Z3_model_eval(ctx,
                              model,
                              to_eval,
                              false, // no model completion
                              &result_ast);
  if (!result) {
    return FALSE;
  }
  return z3_ast_to_term_internal(result_ast, result_term);
}



Z3_symbol mk_symbol(Z3_context ctx, term_t formula) {

  const int term_type = PL_term_type(formula);

  switch (term_type) {
  case PL_ATOM: {
    char *chars;
    int res = PL_get_atom_chars(formula, &chars);
    assert(res);
    DEBUG("mk_symbol got atom %s\n", chars);
    Z3_symbol s = Z3_mk_string_symbol(ctx, chars);
    return s;
    break;
  }
  case PL_VARIABLE: {
    char *chars;
    int res = PL_get_chars(formula, &chars, CVT_WRITE);
    assert(res);
    INFO("mk_symbol got variable %s\n", chars);
    Z3_symbol s = Z3_mk_string_symbol(ctx, chars);
    return s;
    break;
  }
  case PL_STRING: {
    char *string;
    size_t len;
    int res = PL_get_string_chars(formula, &string, &len);
    assert(res);
    Z3_symbol s = Z3_mk_string_symbol(ctx, string);
    return s;
    break;
  }
  case PL_INTEGER: {
    long lval;
    int res = PL_get_long(formula, &lval);
    assert(res);
    Z3_symbol s = Z3_mk_int_symbol(ctx, lval);
    return s;
    break;
  }
  default: {
    char *fchars;
    int res = PL_get_chars(formula, &fchars, CVT_WRITE);
    assert(res);
    ERROR("error making symbol %s, term type is %d\n", fchars, term_type);
  }
  } // end switch

  return NULL;
}

/*
  For debugging:
*/

foreign_t z3_symbol_foreign(term_t i, term_t symbol) {
  int rval;
  DEBUG("term types: %d %d\n", PL_term_type(i), PL_term_type(symbol));
  Z3_context ctx = get_context();

  Z3_symbol s = mk_symbol(ctx, i);
  if (s == NULL) {
    // return PL_warning("z3_symbol/2: should specify an int, atom, or string");
    return FALSE;
  }
  return PL_unify_pointer(symbol, s);
}


int z3_lbool_to_atom(const Z3_lbool status, term_t plterm) {
  switch (status) {
  case Z3_L_FALSE:
    return PL_unify_atom_chars(plterm, "l_false");
    break;
  case Z3_L_TRUE:
    return PL_unify_atom_chars(plterm, "l_true");
    break;
  case Z3_L_UNDEF:
    return PL_unify_atom_chars(plterm, "l_undef");
    break;
  }
}

/* For debugging only, easy to crash the system :-) */

foreign_t z3_ast_to_term_foreign(term_t ast_term, term_t term) {
  Z3_ast ast;
  PL_get_pointer_ex(ast_term, (void**) &ast);
  return z3_ast_to_term_internal(ast, term);
}


// get a Prolog list with the assertions added to a solver:

foreign_t z3_solver_assertions_foreign(term_t solver_term, term_t list) {
  Z3_solver solver;
  int rval = PL_get_pointer_ex(solver_term, (void **) &solver);
  assert(rval);
  Z3_context ctx = get_context();
  Z3_ast_vector v = Z3_solver_get_assertions(ctx, solver);
  int size = Z3_ast_vector_size(ctx, v);
  DEBUG("Vector size is %d\n", size);
  term_t l = PL_new_term_ref();
  PL_put_nil(l);
  for (unsigned i = 0; i < size; ++i) {
    term_t a = PL_new_term_ref(); // putting this outside the loop does not work.
    Z3_ast termi = Z3_ast_vector_get(ctx, v, i);
    z3_ast_to_term_internal(termi, a);
    int r = PL_cons_list(l, a, l);
    assert(r);
  }
  return PL_unify(l, list);
}




/*
  Converts a Z3 ast to a Prolog term:
*/

foreign_t z3_ast_to_term_internal(Z3_ast ast, term_t term) {
  Z3_context ctx = get_context();
  if (Z3_is_numeral_ast(ctx, ast)) {
    int64_t i;
    if (Z3_get_numeral_int64(ctx, ast, &i)) {
      DEBUG("got numeral %lld\n", i);
      return PL_unify_int64(term, i);
    }
    int64_t num, den;
    if (Z3_get_numeral_rational_int64(ctx, ast, &num, &den)) {
      functor_t div = PL_new_functor(PL_new_atom("div"), 2); // how to construct a Prolog rational?
      term_t t = PL_new_term_ref();
      term_t t1 = PL_new_term_refs(2);
      term_t t2 = t1+1;
      int res = PL_put_int64(t1, num);
      if (!res) return res;
      res = PL_put_int64(t2, den);
      if (!res) return res;
      res = PL_cons_functor(t, div, t1, t2);
      if (!res) {
        ERROR("error calling PL_cons_functor");
        return FALSE;
      }
      return PL_unify(term, t);
    }
  }
  DEBUG("non-numeral case\n");
  if (Z3_is_string(ctx, ast)) {
    Z3_string s = Z3_get_string(ctx, ast);
    DEBUG("got string %s", s);
    return PL_unify_string_chars(term, s);
  }

  // TODO: handle booleans,
  // use Z3_get_bool_value(ctx, ast);

  if (Z3_get_ast_kind(ctx, ast) == Z3_APP_AST) {
    Z3_app app = Z3_to_app(ctx, ast);
    unsigned arity = Z3_get_app_num_args(ctx, app);
    DEBUG("We have a Z3_app_ast of arity %d\n", arity);
    term_t subterms = PL_new_term_refs(arity);
    for (int i=0; i<arity; ++i) {
      Z3_ast subterm_ast = Z3_get_app_arg(ctx, app, i);
      if (!z3_ast_to_term_internal(subterm_ast, subterms+i)) {
        return FALSE;
      }
    }
    Z3_func_decl decl = Z3_get_app_decl(ctx, app);
    Z3_symbol symbol = Z3_get_decl_name(ctx, decl);
    Z3_string str = Z3_get_symbol_string(ctx, symbol);
    term_t t = PL_new_term_ref();
    functor_t func = PL_new_functor(PL_new_atom(str), arity);
    if (!PL_cons_functor_v(t, func, subterms)) {
      return FALSE;
    }
    return PL_unify(term, t);
  }

  INFO("z3_ast_to_term failed\n");
  return FALSE;
}


foreign_t term_to_z3_ast_foreign(term_t formula, term_t result) {
  Z3_context ctx = get_context();
  Z3_ast z3_ast = term_to_ast(ctx, formula);
  if (z3_ast == NULL) {
    return FALSE;
  }
  return PL_unify_pointer(result, z3_ast);
}


/*
  For debugging: convert Z3 ast to a Prolog string:
*/

foreign_t z3_ast_string_foreign(term_t formula, term_t result) {
  Z3_context ctx = get_context();
  Z3_ast z3_form;
  int rval = PL_get_pointer(formula, (void **) &z3_form);
  if (!rval) {
    return rval;
  }
  Z3_string rstring = Z3_ast_to_string(ctx, z3_form);
  return PL_unify_string_chars(result, rstring);
}

/*
  Does one push on the solver; output is the new number of scopes for the solver.
*/

foreign_t z3_solver_push_foreign(const term_t solver_term, term_t output_term) {
  Z3_solver solver;
  int rval = PL_get_pointer(solver_term, (void **) &solver);
  if (!rval) {
    return rval;
  }
  const Z3_context ctx = get_context();
  Z3_solver_push(ctx, solver);
  unsigned scopes = Z3_solver_get_num_scopes(ctx, solver);
  
  return PL_unify_uint64(output_term, scopes);
}

/* Pops the solver npops times. Output is the new number of scopes for the solver. */
   
foreign_t z3_solver_pop_foreign(const term_t solver_term, const term_t npops, term_t output_term) {
  Z3_solver solver;
  int rval = PL_get_pointer(solver_term, (void **) &solver);
  if (!rval) {
    return rval;
  }
  int nbacktrack;
  rval = PL_get_integer_ex(npops, &nbacktrack);
  assert(rval);
  const Z3_context ctx = get_context();
  const int scopes = Z3_solver_get_num_scopes(ctx, solver);
  if (nbacktrack > scopes) {
    ERROR("Cannot pop %d since scopes is %d\n", nbacktrack, scopes);
    return FALSE;
  }
  Z3_solver_pop(ctx, solver, nbacktrack);
  const int new_scopes = Z3_solver_get_num_scopes(ctx, solver);
  assert(new_scopes == scopes - nbacktrack);
  return PL_unify_uint64(output_term, new_scopes);
}

/*
 Assert formula for solver. Creates a new solver if solver_term is a variable.
 FIXME: can crash SWI Prolog by putting in a random int as the solver.
*/

foreign_t z3_assert_foreign(term_t solver_term, term_t formula) {
  int rval;
  const Z3_context ctx = get_context();
  Z3_solver solver;

  if (PL_is_variable(solver_term)) {
    solver = Z3_mk_solver(ctx);
    rval = PL_unify_pointer(solver_term, solver);
    if (!rval) {
      ERROR("making new solver failed %d\n", rval);
      return rval;
    }
    Z3_solver_inc_ref(ctx, solver);
    DEBUG("made new solver %p\n", (void *) solver);
  }
  else {
    rval = PL_get_pointer_ex(solver_term, (void **) &solver);
    if (!rval) {
      DEBUG("unify solver failed %d\n", rval);
      return rval;
    }
  }

  Z3_ast z3_formula = term_to_ast(ctx, formula);

  if (z3_formula == NULL) {
    char *formula_string;
    int res = PL_get_chars(formula, &formula_string, CVT_ALL | CVT_VARIABLE | CVT_EXCEPTION | CVT_WRITE);
    if (!res) {
      ERROR("PL_get_chars failed");
      return FALSE;
    }
    // return PL_warning("z3_assert/3: could not make Z3 formula %s", formula_string); // starts the tracer.
    ERROR("z3_assert/3: could not make Z3 formula %s\n", formula_string);
    return FALSE;
    
  }

  DEBUG("made formula %p\n", (void *) z3_formula);
  Z3_sort formula_sort = Z3_get_sort(ctx, z3_formula);
  if (formula_sort != Z3_mk_bool_sort(ctx)) {
    char * formula_string;
    int res = PL_get_chars(formula, &formula_string, CVT_ALL | CVT_VARIABLE | CVT_EXCEPTION | CVT_WRITE);
    if (!res) {
      ERROR("PL_get_chars failed\n");
      return FALSE;
    }
    ERROR("z3_assert/3: cannot assert non-boolean formula %s\n", formula_string);
    // look into PL_raise_exception
    return FALSE;
  }

  Z3_solver_assert(ctx, solver, z3_formula);
  DEBUG("did assert\n");
  return TRUE;
}


foreign_t z3_solver_scopes_foreign(term_t solver_term, term_t result) {
  Z3_solver solver;
  int rval = PL_get_pointer_ex(solver_term, (void **) &solver);
  if (!rval) {
    return rval;
  }
  const Z3_context ctx = get_context();
  unsigned scopes = Z3_solver_get_num_scopes(ctx, solver);
  return PL_unify_uint64(result, scopes);
}

foreign_t z3_solver_check_foreign(term_t solver_term, term_t status_arg) {
  Z3_solver solver;
  int rval = PL_get_pointer_ex(solver_term, (void **) &solver);
  if (!rval) {
    return rval;
  }
  const Z3_context ctx = get_context();

  Z3_lbool check_status = Z3_solver_check(ctx, solver);
  DEBUG("did check, status %d\n", check_status);
  rval = z3_lbool_to_atom(check_status, status_arg);
  DEBUG("did status to atom %d\n", rval);
  return rval;
}


foreign_t z3_solver_check_and_print_foreign(term_t solver_term, term_t status_arg) {
  Z3_solver solver;
  int rval = PL_get_pointer_ex(solver_term, (void **) &solver);
  if (!rval) {
    return rval;
  }
  const Z3_context ctx = get_context();
  const Z3_lbool check_status = solver_check_and_print(ctx, solver);
  return z3_lbool_to_atom(check_status, status_arg);
}


// the function name is the one being declared; subterms are the types, last one is the result.
// We can call get_function_declaration to avoid redeclaring things;
// the problem is state: if we do so, then we cannot redeclare things from one query to the next,
// unless we reset the declarations at each query.
// Do we even want to share declarations from one query to the next?


Z3_func_decl mk_func_decl(Z3_context ctx, const term_t formula, term_t range) {
   atom_t name;
   size_t arity;
   int res = PL_get_name_arity(formula, &name, &arity);
   if (!res) {
     ERROR("Bad argument to mk_func_decl");
     return NULL;
   }

   const char *name_string = PL_atom_chars(name);
   DEBUG("Making function declaration based on %s/%lu\n", name_string, arity);
   Z3_symbol symbol = Z3_mk_string_symbol(ctx, name_string);
   Z3_sort *domain = malloc(sizeof(Z3_sort) * arity);
   DEBUG("domain is %p\n", domain);
   term_t a = PL_new_term_ref();
   for (int i=1; i<=arity; ++i) {
     int res = PL_get_arg(i, formula, a);
     DEBUG("Argument %d, res is %d\n", i, res);
     if (!res) {
       ERROR("PL_get_arg in mk_func_decl failed\n");
       return NULL;
     }
     domain[i-1] = mk_sort(ctx, a);
     if (domain[i-1] == NULL) {
       INFO("mk_func_decl returning NULL\n");
       return NULL;
     }
     DEBUG("Made domain %s\n", Z3_ast_to_string(ctx, (Z3_ast) domain[i-1]));
   }
   // BUG: range is a variable here.
   Z3_sort range_sort = mk_sort(ctx, range);
   if (range_sort == NULL) {
     ERROR("Got null for range_sort\n");
     char *fchars, *rchars;
     int res = PL_get_chars(formula, &fchars, CVT_WRITE);
     ERROR("Formula was %s\n", fchars);
     res = PL_get_chars(range, &fchars, CVT_WRITE);
     ERROR("Range was %s\n", fchars);
     return NULL;
   }

   Z3_func_decl result = get_function_declaration(ctx, name_string, arity);
   // FIXME: the question is whether we overwrite existing declarations or not.
   if (result == NULL) {
     result = Z3_mk_func_decl(ctx, symbol, arity, arity == 0 ?  0 : domain, range_sort);
     if (result != NULL) {
       register_function_declaration_string(ctx, name_string, arity, result);
       DEBUG("mk_func_decl result is %s\n", Z3_ast_to_string(ctx, Z3_func_decl_to_ast(ctx, result)));
     }
   }
   else {
     DEBUG("Found existing declaration for %s/%ld\n", name_string, arity);
     Z3_func_decl test =  Z3_mk_func_decl(ctx, symbol, arity, arity == 0 ?  0 : domain, range_sort);
     if (test != result) {
       ERROR("New declaration for \"%s\" is different from old one. Try z3_reset_declarations.\n", name_string);
       result = NULL; // FIXME: this avoids silent failure, but unit tests fail, since we are re-declaring things all the time.
       // TODO: try just letting the new one overwrite the old one. Combined with the backtrackable typemap, should be safe.
     }
   }

   free(domain);
   return(result);
}



// Makes a function (or constant) declarations.
// Example: z3_function_declaration(f(int, bool), int, R).
// Example: z3_function_declaration(f(int, int), int, X)

// Note: This does not handle the case where formula is a variable.
// There does not seem to be a way to get the attribute here, so have to pass a fake term, then...

// TODO: require that result is var?

foreign_t z3_function_declaration_foreign(const term_t formula, const term_t range, term_t result) {
  atom_t name;
  size_t arity;
  int res = PL_get_name_arity(formula, &name, &arity);
  if (!res) {
    if (PL_is_variable(formula)) {
      ERROR("should not directly declare Z3 types for variables, use attributes instead\n");
      return FALSE;
    }
    else {
      char *formula_chars = NULL;
      char *range_chars = NULL;
      res = PL_get_chars(formula, &formula_chars, CVT_WRITE);
      res = PL_get_chars(range, &range_chars, CVT_WRITE);
      ERROR("Bad declaration, term %s and range %s\n", formula_chars, range_chars);
      return FALSE;
    }
  }
  if (!PL_is_atom(range)) { // TODO: we could unify it with all the known types... :-)
    ERROR("z3_function_declaration range should be an atom\n");
    return FALSE;
  }
  const Z3_context ctx = get_context();
  Z3_func_decl decl = mk_func_decl(ctx, formula, range);
  if (decl == NULL) {
    DEBUG("failing, mk_func_decl is NULL\n");
    return FALSE;
  }
  return PL_unify_pointer(result, decl);
}


foreign_t model_functions(Z3_context ctx, Z3_model m, term_t list) {
  int num_funcs = Z3_model_get_num_funcs(ctx, m);
  term_t l = PL_new_term_ref();
  PL_put_nil(l);
  DEBUG("Num functions is %d\n", num_funcs);
  for (unsigned i = 0; i < num_funcs; i++) {
    Z3_func_decl fdecl = Z3_model_get_func_decl(ctx, m, i);
    Z3_symbol symbol = Z3_get_decl_name(ctx, fdecl);
    // must be careful with this, next call to Z3_get_symbol_string invalidates it:
    // const Z3_string function_name = Z3_get_symbol_string(ctx, symbol);
    DEBUG("Function is %s\n", Z3_get_symbol_string(ctx, symbol));

    Z3_func_interp finterp = Z3_model_get_func_interp(ctx, m, fdecl);
    if (finterp == NULL) {
      continue;
    }
    Z3_func_interp_inc_ref(ctx, finterp); // crashes without this!

    unsigned arity = Z3_func_interp_get_arity(ctx, finterp);
    DEBUG("Arity is %d\n", arity);

    unsigned fentries = Z3_func_interp_get_num_entries (ctx, finterp);
    DEBUG("Entries is %d\n", fentries);
    for (unsigned j = 0; j < fentries; j++) {
      DEBUG("processing entry %d\n", j);
      Z3_func_entry point = Z3_func_interp_get_entry(ctx, finterp, j);
      Z3_func_entry_inc_ref(ctx, point);
      DEBUG("got point\n");
      Z3_ast value = Z3_func_entry_get_value(ctx, point);
      DEBUG("got value\n");
      unsigned args = Z3_func_entry_get_num_args(ctx, point);
      // assert(args == arity);
      DEBUG("num_args for %d is %d\n", j, args);

      // the lhs f(v1, ..., vn) of the "point":
      term_t lhs = PL_new_term_ref();
      term_t subterms = PL_new_term_refs(arity);

      for (unsigned w = 0; w < args; w++) {
        DEBUG("getting subterm %u\n", w);
        Z3_ast keyw = Z3_func_entry_get_arg(ctx, point, w);
        if (!z3_ast_to_term_internal(keyw, subterms+w)) {
          return FALSE;
        }
      }

      const Z3_string function_name = Z3_get_symbol_string(ctx, symbol);
      DEBUG("Making func using %s\n", function_name);
      functor_t func = PL_new_functor(PL_new_atom(function_name), arity);
      if (!PL_cons_functor_v(lhs, func, subterms)) {
        return FALSE;
      }

      DEBUG("making rhs\n");
      term_t rhs = PL_new_term_ref();
      if (!z3_ast_to_term_internal(value, rhs)) {
        return FALSE;
      }

      DEBUG("consing arrow\n");
      functor_t arrow = PL_new_functor(PL_new_atom("->"), 2);
      term_t pair = PL_new_term_ref();
      if (!PL_cons_functor(pair, arrow, lhs, rhs)) {
        DEBUG("error consing functor\n");
        return FALSE;
      }
      
      DEBUG("consing list\n");
      int r = PL_cons_list(l, pair, l);
      if (!r) {
        return r;
      }
    }
    
    DEBUG("getting the else\n");
    Z3_ast felse = Z3_func_interp_get_else(ctx, finterp);
    term_t else_value = PL_new_term_ref();
    if (!z3_ast_to_term_internal(felse, else_value)) {
      return FALSE;
    }
    functor_t else_functor = PL_new_functor(PL_new_atom("else"), 2);
    term_t else_term = PL_new_term_ref();
    term_t fname_term = PL_new_term_ref();
    const Z3_string function_name = Z3_get_symbol_string(ctx, symbol);
    PL_put_atom_chars(fname_term, function_name);
    if (!PL_cons_functor(else_term, else_functor, fname_term, else_value)) {
      return FALSE;
    }
    if (!PL_cons_list(l, else_term, l)) {
        return FALSE;
    }
    
    Z3_func_interp_dec_ref(ctx, finterp);
  }
  
  return PL_unify(l, list);
} // model_functions


foreign_t model_constants(const Z3_context ctx, const Z3_model m, term_t list) {
  const int num_consts = Z3_model_get_num_consts(ctx, m);
  DEBUG("Num constants is %d\n", num_consts);
  term_t l = PL_new_term_ref();
  PL_put_nil(l);

  for (unsigned i = 0; i < num_consts; i++) {
    Z3_func_decl fdecl = Z3_model_get_const_decl(ctx, m, i);
    Z3_symbol symbol = Z3_get_decl_name(ctx, fdecl);
    // note: must make sure there's no other use of Z3_get_symbol_string between now and when we use constant_name:
    const Z3_string constant_name = Z3_get_symbol_string(ctx, symbol);
    DEBUG("Constant is %s\n", constant_name);

    Z3_ast value = Z3_model_get_const_interp(ctx, m, fdecl);
    if (value == NULL) {
      continue;
    }

    term_t lhs = PL_new_term_ref();
    int res = PL_put_atom_chars(lhs, constant_name); // TODO: macro to check results?
    if (!res) {
      ERROR("PL_put_atom_chars failed\n");
      return FALSE;
    }

    DEBUG("making rhs\n");
    term_t rhs = PL_new_term_ref();
    if (!z3_ast_to_term_internal(value, rhs)) {
      return FALSE;
    }

    DEBUG("consing arrow\n");
    functor_t arrow = PL_new_functor(PL_new_atom("->"), 2);
    term_t pair = PL_new_term_ref();
    if (!PL_cons_functor(pair, arrow, lhs, rhs)) {
      DEBUG("error consing functor\n");
      return FALSE;
    }
      
    DEBUG("consing list\n");
    int r = PL_cons_list(l, pair, l);
    if (!r) {
      return r;
    }
  
  }
  
  return PL_unify(l, list);
} // model_constants


foreign_t z3_model_functions_foreign(term_t model_term, term_t list) {
  const Z3_context ctx = get_context();
  Z3_model model;
  int rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) {
    return rval;
  }
  Z3_model_inc_ref(ctx, model);
  rval = model_functions(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}    

foreign_t z3_model_constants_foreign(term_t model_term, term_t list) {
  Z3_context ctx = get_context();
  Z3_model model;
  int rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) {
    return rval;
  }
  Z3_model_inc_ref(ctx, model);
  rval = model_constants(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}    

Z3_sort mk_sort(Z3_context ctx, term_t expression) {
  switch (PL_term_type(expression)) {
  case PL_ATOM: {
    char *name_string;
    int res = PL_get_atom_chars(expression, &name_string);
    DEBUG("making sort for atom %s\n", name_string);
    if (!res) {
      return FALSE;
    }
    if (strcmp(name_string, "bool") == 0 || strcmp(name_string, "boolean") == 0) {
      DEBUG("returning bool sort\n");
      return Z3_mk_bool_sort(ctx);
    }
    if (strcmp(name_string, "int") == 0 || strcmp(name_string, "integer") == 0) {
      DEBUG("returning int sort\n");
      return Z3_mk_int_sort(ctx);
    }
    if (strcmp(name_string, "float") == 0 || strcmp(name_string, "real") == 0 || strcmp(name_string, "double") == 0) {
      DEBUG("returning sort for float/real/double\n");
      return Z3_mk_real_sort(ctx); // not the same as a floating point number in Z3
      // return Z3_mk_fpa_sort_double(ctx);
    }
    Z3_symbol uninterpreted_name = Z3_mk_string_symbol(ctx, name_string);
    DEBUG("Making uninterpreted sort for %s\n", name_string);
    return Z3_mk_uninterpreted_sort(ctx, uninterpreted_name);
    break;
  }
  case PL_TERM:
    assert(PL_is_compound(expression));
    atom_t name;
    size_t arity;
    int res = PL_get_name_arity(expression, &name, &arity);
    if (!res) {
      ERROR("PL_get_name_arity failed\n");
      return FALSE;
    }

    const char *name_string = PL_atom_chars(name);
    DEBUG("sort expression %s has arity %lu\n", name_string, arity);

    term_t a = PL_new_term_ref();
    Z3_sort *subterms = calloc(arity, sizeof(Z3_sort));
    for (int n=1; n<=arity; n++) {
      res = PL_get_arg(n, expression, a);
      INFO("mk_sort: Argument %d, res is %d\n", n, res);
      if (!res) {
        return FALSE;
      }
      subterms[n-1] = mk_sort(ctx, a); // datatypes use constructors, not subsorts...
      if (subterms[n-1] == NULL) {
        return NULL;
      }
    }
    // for bitvectors, subarg is an int.
    fprintf(stderr, "WARN - need to finish compound case for mk_sort\n");
    return NULL;
    break;
  case PL_VARIABLE: {
    // We'll do this in Prolog, rather than here, so fail:
    fprintf(stderr, "WARN - mk_sort can't take variables\n");
    return NULL;
    /********
    DEBUG("making sort for variable\n");
    // generate a new symbol
    global_symbol_count += 1;
    char newname[100];
    snprintf(newname, sizeof(newname), "undef_sort_%d", global_symbol_count);
    term_t a = PL_new_term_ref();
    PL_put_atom_chars(a, newname);
    DEBUG("unifying type variable with %s\n", newname);
    int res = PL_unify(a, expression);
    assert(res);
    Z3_symbol Uninterpreted_name = Z3_mk_string_symbol(ctx, newname);
    return Z3_mk_uninterpreted_sort(ctx, Uninterpreted_name);
    ******/
  }
  default:
      fprintf(stderr, "WARN - unimplemented mk_sort\n");
      return NULL;
  }
  assert(false); // unreachable
}


/*
  Converts the Prolog term "formula" to a Z3 AST.
  Returns NULL if it fails:
*/

Z3_ast term_to_ast(const Z3_context ctx, const term_t formula) {
  long lval;
  Z3_ast result = NULL;
  switch (PL_term_type(formula)) {

  case PL_VARIABLE:
    // TODO: it could be nice to look at the attributes, if any, and use them instead of the variable,
    // but the foreign interface does not offer methods for doing so.
    return NULL;
  case PL_ATOM: {
    int bval;
    if (PL_get_bool(formula, &bval)) {
      DEBUG("Got boolean\n");
      if (bval) {
        return Z3_mk_true(ctx);
      }
      return Z3_mk_false(ctx);
    }

    char *chars;
    int res = PL_get_atom_chars(formula, &chars);
    if (!res) {
      return NULL;
    }
    DEBUG("Got atom %s\n", chars);
    
    // chars is set
    const Z3_func_decl declaration = get_function_declaration(ctx, chars, 0);
    if (declaration == NULL) {
      DEBUG("did not find declaration for %s, defaulting to int\n", chars);
    }
    else {
      const Z3_string decstring  = Z3_ast_to_string(ctx, Z3_func_decl_to_ast(ctx, declaration));
      DEBUG("Got declaration %s\n", decstring);
    }
    if (declaration == NULL) { // Undeclared atoms are by default ints; we could require everything to be declared.
      DEBUG("term_to_ast got atom %s, default int\n", chars);
      result = mk_int_var(ctx, chars); // TODO: require declarations
    }
    else {
      result = Z3_mk_app(ctx, declaration, 0, 0); // arity 0, no args
    }
    return result;
    break;
  }
  case PL_STRING: {
    char *string;
    size_t len;
    if (!PL_get_string_chars(formula, &string, &len)) {
      ERROR("Could not convert string\n");
    }
    else {
      return Z3_mk_string(ctx, string);
    }
    return NULL;
    break;
  }
  case PL_INTEGER:
    if (PL_get_long_ex(formula, &lval)) {
      DEBUG("Got PL_get_long\n");
      Z3_sort intsort = Z3_mk_int_sort(ctx);
      return Z3_mk_int64(ctx, lval, intsort);
    }
    else {
      ERROR("Could not get long in PL_INTEGER case\n");
      return NULL;
    }
    break;
  case PL_RATIONAL:
    ERROR("TODO: PL_RATIONAL\n");
    break;
  case PL_FLOAT: {
    // double myf;
    // don't use PL_get_float because apparently Z3 can't make reals from floats.
    // Z3_sort sort = Z3_mk_fpa_sort_double(ctx);
    DEBUG("making float\n");
    Z3_sort sort = Z3_mk_real_sort(ctx);
    char *formula_string;
    if (PL_get_chars(formula, &formula_string, CVT_FLOAT) ) {
      result = Z3_mk_numeral(ctx, formula_string, sort);
      if (result == NULL) {
        ERROR("Z3_mk_numeral failed for %s\n", formula_string);
      }
      return result;
    }
    else {
      ERROR("PL_get_chars failed for float %s\n", formula_string);
      return NULL;
    }
    break;
  }
  case PL_TERM:
    assert(PL_is_compound(formula));
    atom_t name;
    size_t arity;
    int res = PL_get_name_arity(formula, &name, &arity);
    if (!res) {
      return NULL;
    }
    DEBUG("arity is %lu\n", arity);

    const char *name_string = PL_atom_chars(name);
    DEBUG("functor name: %s\n", name_string);

    if (strcmp(name_string, ":")==0) { // Path in case : is not handled at the Prolog level.
      // we expect symbol:sort
      if (arity != 2) {
        ERROR(": should have arity 2, but has arity %lu", arity);
        return NULL;
      }
      term_t name_term = PL_new_term_ref();
      res = PL_get_arg(1, formula, name_term);
      if (!res) {
        ERROR("PL_get_arg 1 failed\n");
        return NULL;
      }
      Z3_symbol symbol_name = mk_symbol(ctx, name_term);
      term_t range = PL_new_term_ref();
      res = PL_get_arg(2, formula, range);
      if (!res) {
        ERROR("PL_get_arg 2 failed\n");
        return NULL;
      }
      Z3_sort sort = mk_sort(ctx, range);
      if (sort == NULL) {
        INFO("mk_sort for symbol is null\n");
        return NULL;
      }
      // FIXME: We are converting PL to Z3. We should declare...
      // mk_func_decl(ctx, symbol_name, ...);
      // to catch inconsistent uses of the same constant.
      atom_t name_atom;
      res = PL_get_atom(name_term, &name_atom);
      DEBUG("Declaring for %s\n", name_string);
      Z3_func_decl decl = mk_func_decl(ctx, name_term, range);
      if (decl == NULL) {
        ERROR("Failed making decl\n");
        return NULL;
      }
      DEBUG("making const\n");
      result = Z3_mk_const(ctx, symbol_name, sort);
      DEBUG("making const result is %s\n", Z3_ast_to_string(ctx, result));
      return result;
    }

    term_t a = PL_new_term_ref();
    Z3_ast *subterms = calloc(arity, sizeof(Z3_ast));
    for (int n=1; n<=arity; ++n) {
      res = PL_get_arg(n, formula, a);
      DEBUG("term_to_ast: Argument %d, res is %d\n", n, res);
      assert(res);
      subterms[n-1] = term_to_ast(ctx, a);
      if (subterms[n-1] == NULL) {
        INFO("Making subterm %d failed\n", n);
        free(subterms);
        return NULL;
      }
      DEBUG("Made subterm %d, %s\n", n, Z3_ast_to_string(ctx, subterms[n-1]));
    }

    if ( strcmp(name_string, "+") == 0 ) {result = Z3_mk_add(ctx, arity, subterms);}
    else if (strcmp(name_string, "*") == 0 ) {result = Z3_mk_mul(ctx, arity, subterms);}
    else if (strcmp(name_string, "-") == 0 || strcmp(name_string, "minus") == 0 ) {
      if (arity == 1) {
        result = Z3_mk_unary_minus(ctx, subterms[0]);
      }
      else {
        result = Z3_mk_sub(ctx, arity, subterms);
      }
    }
    else if (strcmp(name_string, "div") == 0 || strcmp(name_string, "/") == 0) {
      assert(arity == 2);
      DEBUG("making div\n");
      result = Z3_mk_div(ctx, subterms[0], subterms[1]);
      // The arguments must either both have int type or both have real type.
      // division by 0 is allowed, can be anything
      DEBUG("result is %s\n", Z3_ast_to_string(ctx, result));
    }
    else if (strcmp(name_string, "mod") == 0) {assert(arity == 2); result = Z3_mk_mod(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "rem") == 0) {assert(arity == 2); result = Z3_mk_rem(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "power") == 0 || strcmp(name_string, "**") == 0) {
      assert(arity == 2);
      result = Z3_mk_power(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "<") == 0) {assert(arity == 2); result = Z3_mk_lt(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "=<") == 0 || strcmp(name_string, "leq") == 0) {
      assert(arity == 2);
      result = Z3_mk_le(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, ">") == 0) {assert(arity == 2); result = Z3_mk_gt(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, ">=") == 0 || strcmp(name_string, "geq") == 0) {
      assert(arity == 2);
      result = Z3_mk_ge(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "isint") == 0) {assert(arity == 1); result = Z3_mk_is_int(ctx, subterms[0]);}
    // crashes: {int2real(1.0) = X}.
    // else if (strcmp(name_string, "int2real") == 0) {assert(arity == 1); result = Z3_mk_int2real(ctx, subterms[0]);}
    // else if (strcmp(name_string, "real2int") == 0) {assert(arity == 1); result = Z3_mk_real2int(ctx, subterms[0]);}
    else if (strcmp(name_string, "=") == 0 || strcmp(name_string, "==") == 0 || strcmp(name_string, "equals") == 0 ) {
      DEBUG("making equals\n");
      assert(arity == 2);
      // Check that types are compatible; otherwise Z3 quits/crashes
      Z3_sort s1 = Z3_get_sort(ctx, subterms[0]);
      Z3_sort s2 = Z3_get_sort(ctx, subterms[1]);
      if (s1 != s2) {
        ERROR("different types for equals, failing\n");
        return NULL;
      }
      DEBUG("making equals\n");
      result = Z3_mk_eq(ctx, subterms[0], subterms[1]);
      DEBUG("made equals\n");
    }
    else if (strcmp(name_string, "distinct") == 0 ) {result = Z3_mk_distinct(ctx, arity, subterms);}
    else if (strcmp(name_string, "not") == 0 ) {
      assert(arity == 1);
      result = Z3_mk_not(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "ite") == 0 ) {
       assert(arity == 3);
       result = Z3_mk_ite(ctx, subterms[0], subterms[1], subterms[2]);
    }
    else if (strcmp(name_string, "iff") == 0 ) {assert(arity == 2); result = Z3_mk_iff(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "implies") == 0 ) {assert(arity == 2); result = Z3_mk_implies(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "xor") == 0 ) {assert(arity == 2); result = Z3_mk_xor(ctx, subterms[0], subterms[1]);}
    else if (strcmp(name_string, "<>") == 0 ) {assert(arity == 2); 
            Z3_sort s1 = Z3_get_sort(ctx, subterms[0]);
            Z3_sort s2 = Z3_get_sort(ctx, subterms[1]);
            if (s1 != s2) {
                ERROR("different types for <>, always true\n");
                result = Z3_mk_true(ctx);
            }
            else {
                result = Z3_mk_not(ctx, Z3_mk_eq(ctx, subterms[0], subterms[1]));
                }
            }
    else if (strcmp(name_string, "and") == 0 ) {result = Z3_mk_and(ctx, arity, subterms);}
    else if (strcmp(name_string, ",") == 0 ) {result = Z3_mk_and(ctx, arity, subterms);}
    else if (strcmp(name_string, "or") == 0 ) {result = Z3_mk_or(ctx, arity, subterms);}
    else if (strcmp(name_string, ";") == 0 ) {result = Z3_mk_or(ctx, arity, subterms);}
    else if (strcmp(name_string, "atleast") == 0) {
      unsigned k;
      if (!Z3_get_numeral_uint(ctx, subterms[arity-1], &k)) {
        ERROR("last argument of atleast should be an int\n");
        result = NULL;
      }
      else {
        result = Z3_mk_atleast(ctx, arity-1, subterms, k);
      }
    }
    else if (strcmp(name_string, "atmost") == 0) {
      unsigned k;
      if (!Z3_get_numeral_uint(ctx, subterms[arity-1], &k)) {
        ERROR("last argument of atmost should be an int\n");
        result = NULL;
      }
      else {
        result = Z3_mk_atmost(ctx, arity-1, subterms, k);
      }
    }
    else { // uninterpreted function
      DEBUG("Making function declaration for %s\n", name_string);
      Z3_func_decl declaration = get_function_declaration(ctx, name_string, arity);
      if (declaration == NULL) {
        INFO("Could not find declaration for %s/%lu\n", name_string, arity);
        return NULL;
      }
      result = Z3_mk_app(ctx, declaration, arity, subterms);
    }
    free(subterms);
    DEBUG("freed subterms\n");
    return result;
    break;
  case PL_NIL:
  case PL_BLOB:
  case PL_LIST_PAIR:
  case PL_DICT:
  default: {
    char *formula_string;
    int type = PL_term_type(formula);
    if (! PL_get_chars(formula, &formula_string, CVT_ALL | CVT_VARIABLE | CVT_EXCEPTION | CVT_WRITE) ) {
      ERROR("PL_get_chars failed in term_to_ast for unhandled Prolog term of type %d", type);
    }
    else {
      ERROR("Can't handle formula %s, type is %d\n", formula_string, type);
    }
    break;
    // return Z3_mk_false(ctx);
  }
  } // end switch
  return result;
}


foreign_t z3_simplify_term_foreign(term_t tin, term_t tout) {
  Z3_context ctx = get_context();
  Z3_ast ast_in = term_to_ast(ctx, tin);
  if (ast_in == NULL) {
    return FALSE;
  }
  Z3_ast ast_out = Z3_simplify(ctx, ast_in);
  if (ast_out == NULL) {
    return FALSE;
  }
  return z3_ast_to_term_internal(ast_out, tout);
}


#define PRED(name, arity, func, attr) \
  PL_register_foreign_in_module("z3_swi_foreign", name, arity, func, attr)


install_t install()
{
  fprintf(stderr, "Installing Z3 package\n");
  z3_swi_initialize();

  // name, arity, function, flags

  // get the global context:
  PRED("z3_context", 1, z3_context_foreign, 0);

  // make a new solver:
  PRED("z3_mk_solver", 1, z3_mk_solver_foreign, 0);
  
  PRED("z3_free_solver", 1, z3_free_solver_foreign, 0);
  PRED("z3_free_model", 1, z3_free_model_foreign, 0);
  


  // z3_assert(+Solver, +Formula):
  PRED("z3_assert", 2, z3_assert_foreign, 0);

  // for debugging, testing round-trips:
  PRED("term_to_z3_ast", 2, term_to_z3_ast_foreign, 0);
  PRED("z3_ast_string", 2, z3_ast_string_foreign, 0);
  PRED("z3_ast_to_term", 2, z3_ast_to_term_foreign, 0);
  PRED("z3_symbol", 2, z3_symbol_foreign, 0); // for debugging
  
  PRED("z3_function_declaration", 3, z3_function_declaration_foreign, 0); // +pl_term, +range_atom, -declaration_pointer

  PRED("z3_solver_push", 2, z3_solver_push_foreign, 0); // +solver, -num_scopes
  
  PRED("z3_solver_pop", 3, z3_solver_pop_foreign, 0); // +solver, +numpops, -num_scopes
  
  PRED("z3_solver_scopes", 2, z3_solver_scopes_foreign, 0); // +solver, -num_scopes):

  PRED("z3_solver_check", 2, z3_solver_check_foreign, 0); // +solver, -status
  PRED("z3_solver_check_and_print", 2, z3_solver_check_and_print_foreign, 0); // +solver, -status
  
  PRED("z3_declarations_string", 1, z3_declarations_string_foreign, 0); // -string
  PRED("z3_declaration_map_size", 1, z3_declaration_map_size_foreign, 0); // -size_int
  
  PRED("z3_solver_get_model", 2, z3_solver_get_model_foreign, 0); // +solver, -model_pointer
  PRED("z3_model_eval", 3, z3_model_eval_foreign, 0); // +model_pointer, +formula, -value

  PRED("z3_reset_declarations", 0, z3_reset_declarations_foreign, 0);
  PRED("z3_simplify_term", 2, z3_simplify_term_foreign, 0); // +term, -simplified_term

  PRED("z3_solver_assertions", 2, z3_solver_assertions_foreign, 0); // +solver_pointer, -assertion_list

  PRED("z3_model_functions", 2, z3_model_functions_foreign, 0); // +model_pointer, -functions_term
  PRED("z3_model_constants", 2, z3_model_constants_foreign, 0); // +model_pointer, -constants_term

}
