
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>

#include <pthread.h>

// /opt/homebrew/Cellar/gmp/6.3.0/include/gmp.h
#include <gmp.h>
#include <SWI-Prolog.h>

#include <z3.h>

/****

     This is a C foreign interface between SWI Prolog and the Z3 prover. It exposes the basic Z3 functionality
     as Prolog predicates, leaving the implementation of more complex applications to Prolog code and libraries.

     The main decision is how to handle state -- context, declarations and solvers.

     It would be nice to embed all the function declarations in the context object; for this, we define a "HandleStruct" object
     that has the Z3 context, plus the function declarations.

     This includes enums and enum sorts. However, while normal declarations can be reset without having to create a new context,
     enums can't be reset without resetting the context too.

     We now dynamically allocate HandleStruct objects, for greater flexibility at the app level.
     The solver is bundled in the handler. They could be separated, but would be more error prone at the PL level.

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

#define CHECK_ARITY(symbol, expected, arity) do {if (arity != expected) {ERROR("%s should have arity %d but has arity %lu\n", symbol, expected, arity); return NULL; }} while (false)

#define MK_NUMERAL "mk_numeral"


// To raise Prolog errors, we could use PL_raise_exception, but the _ex functions are recommended instead.

// *************************************************************************

bool numeric_sort(Z3_context ctx, Z3_sort s) {
  Z3_sort_kind k = Z3_get_sort_kind(ctx, s);
  return (k == Z3_BOOL_SORT || k == Z3_INT_SORT || k == Z3_REAL_SORT);
}

Z3_ast mk_int_var(Z3_context ctx, const char * name) {
  Z3_sort INT_SORT = Z3_mk_int_sort(ctx);
  Z3_sort ty = INT_SORT;
  Z3_symbol s = Z3_mk_string_symbol(ctx, name);
  return Z3_mk_const(ctx, s, ty);
}

// Any binary term will work as the key (here, choose "div").
// In Prolog, we convert them to f/N terms --- see z3_enum_declarations and z3_declarations.

Z3_ast mk_ast_key(Z3_context ctx, const char * name, const int64_t arity)
{
  Z3_sort INT_SORT = Z3_mk_int_sort(ctx);
  Z3_ast v1 = mk_int_var(ctx, name);
  Z3_ast v2 = Z3_mk_int64(ctx, arity, INT_SORT);
  return Z3_mk_div(ctx, v1, v2); // closest to F/N
}

// From Z3 examples/c/test_capi.c:
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
    return result;
}


typedef Z3_ast_map decl_map;
typedef Z3_ast_map sort_map;

// ***************************** GLOBAL VARIABLES ********************************************


static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static long handle_counter = 0;

// The HandleStruct has the objects needed to typecheck and convert Prolog terms to Z3.
// Solver and Model objects are separate, and we can do push and pop on solvers from Prolog.

struct HandleStruct {
  Z3_context ctx;
  Z3_solver solver;
  sort_map enum_sorts;  // map from names to Z3 enumeration sorts, used for building terms
  decl_map enum_declarations; // declarations that typechecker will need
  decl_map declarations; // standard declarations
  long handle_id; // used as a unique ID for the context
  Z3_sort int_sort, bool_sort, real_sort;
};

typedef struct HandleStruct *handle;

static functor_t pair_functor; // "="
static functor_t declaration_pair_functor; // ":"

// forward declarations:
Z3_ast term_to_ast(handle h, decl_map map, term_t formula);
foreign_t z3_ast_to_term_internal(Z3_context ctx, Z3_ast ast, term_t formula);
Z3_sort mk_sort(handle h, term_t formula);
Z3_symbol mk_symbol(Z3_context ctx, term_t formula);

void free_handle_contents(handle h);

void z3_swi_error_handler(Z3_context ctx, Z3_error_code e) {
  Z3_string msg = Z3_get_error_msg(ctx, e);
  fprintf(stderr, "Z3 ERROR: code %ul %s\n", e, msg);
}

void initialize_handle(handle handle) {
  DEBUG("Initializing handle %p\n", handle);

  pthread_mutex_lock(&mutex);
  
  Z3_config config = Z3_mk_config();  
  handle->ctx = Z3_mk_context(config);
  Z3_context ctx = handle->ctx;
  DEBUG("Made context %p\n", ctx);

  Z3_solver solver = Z3_mk_solver(ctx);
  handle->solver = solver;
  DEBUG("Made solver %p\n", solver);
  Z3_solver_inc_ref(ctx, solver);

  Z3_set_error_handler(ctx, z3_swi_error_handler);
  Z3_del_config(config);

  handle->enum_sorts = Z3_mk_ast_map(ctx);
  Z3_ast_map_inc_ref(ctx, handle->enum_sorts);

  handle->enum_declarations = Z3_mk_ast_map(ctx);
  Z3_ast_map_inc_ref(ctx, handle->enum_declarations);

  handle->declarations = Z3_mk_ast_map(ctx);
  Z3_ast_map_inc_ref(ctx, handle->declarations);

  handle->int_sort = Z3_mk_int_sort(ctx);
  handle->bool_sort = Z3_mk_bool_sort(ctx);
  handle->real_sort = Z3_mk_real_sort(ctx);

  pthread_mutex_unlock(&mutex);
}

// TODO: Z3_solver_get_statistics

// TODO: make this handle_stats(h, A, B, C), print in PL.

foreign_t handle_stats_foreign(term_t handle_term, term_t num_declarations, term_t num_enum_sorts, term_t num_enum_declarations) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  
  Z3_context ctx = h->ctx;
  uint64_t decl_size = Z3_ast_map_size(ctx, h->declarations);
  int res = PL_unify_uint64(num_declarations, decl_size);
  if (!res) return res;
  uint64_t enum_sorts_size = Z3_ast_map_size(ctx, h->enum_sorts);
  res = PL_unify_uint64(num_enum_sorts, enum_sorts_size);
  if (!res) return res;
  uint64_t enum_declarations_size =  Z3_ast_map_size(ctx, h->enum_declarations);
  res = PL_unify_uint64(num_enum_declarations, enum_declarations_size);
  if (!res) return res;
  
  return TRUE;
}


foreign_t z3_new_handle_foreign(term_t handle_term) {
  if (!PL_is_variable(handle_term)) {
    ERROR("z3_new_handle should be called on a variable");
    return FALSE;
  }
  handle h = malloc(sizeof(struct HandleStruct));
  memset(h, 0, sizeof(struct HandleStruct));
  handle_counter += 1;
  h->handle_id = handle_counter;
  initialize_handle(h);
  int res = PL_unify_pointer(handle_term, h);
  if (!res) {
    ERROR("error in z3_new_handle.");
    free_handle_contents(h);
    free(h);
  }
  INFO("Made new handle %p\n", h);
  return res;
}

foreign_t z3_free_handle_foreign(term_t handle_term) {
  handle h;  
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  INFO("Freeing handle %p\n", h);
  pthread_mutex_lock(&mutex);
  free_handle_contents(h);
  free(h);
  pthread_mutex_unlock(&mutex);
  return TRUE;
}

foreign_t z3_finalize_memory_foreign() {
  Z3_finalize_memory();
  return TRUE;
}

// Not enough: the context remembers the enums.
// foreign_t z3_reset_enums_foreign() {
//  Z3_context ctx = global_context->ctx;
//  Z3_ast_map_reset(ctx, global_context->enum_sorts);
//  Z3_ast_map_reset(ctx, global_context->enum_declarations);
//  return TRUE;
// }


// resets declarations but not enums, which cannot be reset in the same way:
foreign_t z3_reset_declarations_foreign(term_t handle_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_ast_map_reset(h->ctx, h->declarations);
  return TRUE;
}

/* Frees everything except for the handle itself. */

void free_handle_contents(handle h) {
  Z3_context ctx = h->ctx;
  DEBUG("freeing handle contents for %p\n", ctx);

  unsigned scopes = Z3_solver_get_num_scopes(ctx, h->solver);
  INFO("Scopes when freeing is %u\n", scopes);
  Z3_solver_pop(ctx, h->solver, scopes);
  Z3_solver_reset(ctx, h->solver);
  Z3_solver_dec_ref(ctx, h->solver);
  
  Z3_ast_map_reset(ctx, h->declarations);
  Z3_ast_map_reset(ctx, h->enum_sorts);
  Z3_ast_map_reset(ctx, h->enum_declarations);

  // for good measure:
  Z3_ast_map_dec_ref(ctx, h->declarations);
  Z3_ast_map_dec_ref(ctx, h->enum_sorts);
  Z3_ast_map_dec_ref(ctx, h->enum_declarations);

  Z3_del_context(ctx);

}

/****
// worth it? Simpler to just get a new handle.
foreign_t z3_reset_handle_foreign(term_t handle_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  free_handle_contents(h);

  handle_counter += 1;
  h->handle_id = handle_counter; // a random ID would do too.

  initialize_handle(h);

  return TRUE;
}
***/

// ************************* END GLOBALS *************************


// We need function declarations to make terms.

Z3_func_decl get_function_declaration(Z3_context ctx, decl_map declaration_map, const char *name_string, const size_t arity) {
  assert(declaration_map != NULL);
  
  int map_size = Z3_ast_map_size(ctx, declaration_map);
  DEBUG("current map size is %d\n", map_size);
  Z3_ast key = mk_ast_key(ctx, name_string, arity);
  DEBUG("made key %s\n", Z3_ast_to_string(ctx, key));
  if (!Z3_ast_map_contains(ctx, declaration_map, key)) {
    DEBUG("key %s not in map\n", name_string);
    return NULL;
  }
  DEBUG("key %s is in get_function_declaration map\n", name_string);
  Z3_ast value = Z3_ast_map_find(ctx, declaration_map, key);
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


void register_function_declaration(Z3_context ctx, decl_map declaration_map, Z3_symbol name_symbol, const size_t arity, Z3_func_decl declaration) {
  Z3_string name_string = Z3_get_symbol_string(ctx, name_symbol);
  Z3_ast key = mk_ast_key(ctx, name_string, arity); // copies name_string, hopefully
  // the insert replaces any previous one.
  Z3_ast_map_insert(ctx, declaration_map, key, (Z3_ast) declaration);
}

/****
     for debugging; gets the declarations string into result:
***/
foreign_t z3_declarations_string_foreign(term_t handle_term, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  decl_map declaration_map = h->declarations;
  Z3_context ctx = h->ctx;
  Z3_string rstring =  Z3_ast_map_to_string(ctx, declaration_map);
  return PL_unify_string_chars(result, rstring);
}

foreign_t z3_enums_string_foreign(term_t handle_term, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  decl_map declaration_map = h->enum_declarations;
  Z3_context ctx = h->ctx;
  Z3_string rstring =  Z3_ast_map_to_string(ctx, declaration_map);
  return PL_unify_string_chars(result, rstring);
}


/*
  makes a new solver and unifies it with the arg; not needed now.
*/

/**
foreign_t z3_make_solver_foreign(term_t handle_term, term_t solver_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h); // TODO: use ||
  if (!rval) return rval;
  if (!PL_is_variable(solver_term)) {
    ERROR("z3_make_solver should be called on a variable");
    return FALSE;
  }
  Z3_context ctx = h->ctx;
  Z3_solver solver = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, solver); // should be freed with z3_free_solver
  DEBUG("made solver %p\n", (void *) solver );
  return PL_unify_pointer(solver_term, solver);
}
*/


/**
   Frees the solver, which must be an instantiated solver object.
   In Prolog, we can use setup_call_cleanup to do this automatically.
**/

/*
foreign_t z3_free_solver_foreign(term_t handle_term, term_t u) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  
  Z3_solver solver;
  rval = PL_get_pointer_ex(u, (void **) &solver);
  if (!rval) {
    return rval;
  }
  DEBUG("freeing solver %p\n", (void *) solver);
  Z3_solver_dec_ref(h->ctx, solver);
  return TRUE;
}
*/

foreign_t z3_free_model_foreign(term_t handle_term, term_t model_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  Z3_model model;
  rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) return rval;

  DEBUG("freeing model %p\n", (void *) model);
  Z3_model_dec_ref(h->ctx, model);
  return TRUE;
}

/*
  Gets a model object from the solver; "Z3_solver_check" must have been run on the solver first.
  Otherwise, an error is reported and we fail.
  Unsafe, used for model_eval in Prolog; preferably use z3_model/1.
  Model should be freed after use, with z3_free_model/2.
*/

foreign_t z3_get_model_foreign(term_t handle_term, term_t model_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  Z3_solver solver = h->solver;

  Z3_model model = Z3_solver_get_model(h->ctx, solver);
  
  if (model && PL_unify_pointer(model_term, model)) {
    Z3_model_inc_ref(h->ctx, model);
    return TRUE;
  }
  return FALSE;
}



foreign_t z3_model_eval_foreign(term_t handle_term, term_t model_term, term_t term_to_eval, term_t completion_flag, term_t result_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  Z3_model model;
  rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) return rval;

  int completion = FALSE;
  rval = PL_get_bool_ex(completion_flag, &completion);
  if (!rval) return rval;

  Z3_ast to_eval = term_to_ast(h, h->declarations, term_to_eval);
  if (to_eval == NULL) {
    return FALSE; // Future: could return a status atom explaining what happened.
  }
  Z3_ast result_ast;
  bool result = Z3_model_eval(h->ctx,
                              model,
                              to_eval,
                              completion,
                              &result_ast);
  if (!result) {
    return FALSE;
  }
  return z3_ast_to_term_internal(h->ctx, result_ast, result_term);
}



// Makes a Z3 symbol based on a Prolog term "pl_term":

Z3_symbol mk_symbol(Z3_context ctx, term_t pl_term) {

  const int term_type = PL_term_type(pl_term);

  switch (term_type) {
  case PL_ATOM: {
    char *chars;
    int res = PL_get_atom_chars(pl_term, &chars);
    if (!res) return NULL;
    DEBUG("mk_symbol got atom %s\n", chars);
    Z3_symbol s = Z3_mk_string_symbol(ctx, chars);
    return s;
    break;
  }
  case PL_VARIABLE: {
    char *chars;
    int res = PL_get_chars(pl_term, &chars, CVT_WRITE);
    if (!res) return NULL;
    DEBUG("mk_symbol got variable %s\n", chars);
    Z3_symbol s = Z3_mk_string_symbol(ctx, chars);
    return s;
    break;
  }
  case PL_STRING: {
    char *string;
    size_t len;
    int res = PL_get_string_chars(pl_term, &string, &len);
    if (!res) return NULL;
    Z3_symbol s = Z3_mk_string_symbol(ctx, string);
    return s;
    break;
  }
  case PL_INTEGER: {
    long lval;
    int res = PL_get_long(pl_term, &lval);
    if (!res) return NULL;
    Z3_symbol s = Z3_mk_int_symbol(ctx, lval);
    return s;
    break;
  }
  default: {
    char *fchars = NULL;
    int res = PL_get_chars(pl_term, &fchars, CVT_WRITE);
    ERROR("error making symbol %s, term type is %d\n", fchars, term_type);
    return NULL;
  }
  } // end switch

  return NULL;
}


bool z3_sort_to_term(Z3_context ctx, Z3_sort sort, term_t result) {

  Z3_symbol sname = Z3_get_sort_name(ctx, sort);
  Z3_sort_kind kind = Z3_get_sort_kind(ctx, sort);
  int size_int;
  term_t cons_term = PL_new_term_ref();
  switch (kind) {
  case Z3_BV_SORT:
    size_int = Z3_get_bv_sort_size(ctx, sort);
    term_t size_term = PL_new_term_ref();
    int res = PL_put_int64(size_term, size_int);
    functor_t f = PL_new_functor(PL_new_atom(Z3_get_symbol_string(ctx, sname)), 1);
    if (!PL_cons_functor(cons_term, f, size_term)) {
      return FALSE;
    }
    break;
  default:
    {
      Z3_string sname_string = Z3_get_symbol_string(ctx, sname);
      int res = PL_put_atom_chars(cons_term, sname_string);
    }

  } // end switch
  return PL_unify(cons_term, result);
}


// works for the function declaration map, not the sort declarations one:
foreign_t z3_declaration_map_to_term(Z3_context ctx, decl_map declaration_map, term_t result) {

  Z3_ast_vector keys = Z3_ast_map_keys(ctx, declaration_map);
  Z3_ast_vector_inc_ref(ctx, keys);
  unsigned size = Z3_ast_vector_size(ctx, keys);

  term_t l = PL_new_term_ref();
  PL_put_nil(l);

  for (unsigned i = 0; i < size; i++) {
    Z3_ast key = Z3_ast_vector_get(ctx, keys, i);
    term_t key_term = PL_new_term_ref();
    z3_ast_to_term_internal(ctx, key, key_term);

    Z3_func_decl value = (Z3_func_decl) Z3_ast_map_find(ctx, declaration_map, key);
    term_t value_term = PL_new_term_ref();

    // Z3_symbol s = Z3_get_decl_name(ctx, value);

    Z3_sort sort = Z3_get_range(ctx, value);
    Z3_symbol sname = Z3_get_sort_name(ctx, sort);

    bool res = z3_sort_to_term(ctx, sort, value_term);

    term_t pair = PL_new_term_ref();
    if (!PL_cons_functor(pair, declaration_pair_functor, key_term, value_term)) {
      ERROR("error consing functor\n");
      Z3_ast_vector_dec_ref(ctx, keys);
      return FALSE;
    }
    int r = PL_cons_list(l, pair, l);
    if (!r) {
      Z3_ast_vector_dec_ref(ctx, keys);
      return r;
    }
  }
  Z3_ast_vector_dec_ref(ctx, keys);
  return PL_unify(l, result);
}

foreign_t z3_get_enum_declarations_foreign(term_t handle_term, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  return z3_declaration_map_to_term(h->ctx, h->enum_declarations, result);
}

foreign_t z3_get_declarations_foreign(term_t handle_term, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  return z3_declaration_map_to_term(h->ctx, h->declarations, result);
}


// Declare enumerations:
// can only be called once for a given enum name, per context.
// The resulting Z3_sort can be used by mk_var(ctx, varname, sort) or mk_func_decl.
// enums are accumulated in h->enum_declarations.

// +atom, +list
foreign_t z3_declare_enum_foreign(term_t handle_term, term_t sort_name_term, term_t enum_names_list) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  Z3_context ctx = h->ctx;
  const Z3_symbol sort_name = mk_symbol(ctx, sort_name_term);

  if (!PL_is_atom(sort_name_term)) {
    ERROR("z3_declare_enum name should be an atom\n");
    return FALSE;
  }
  if (!PL_is_list(enum_names_list) || !PL_is_ground(enum_names_list)) {
    ERROR("z3_declare_enum range should be a ground list\n");
    return FALSE;
  }

  char * sort_name_string;
  int res = PL_get_atom_chars(sort_name_term, &sort_name_string);
  if (!res) {
    return res;
  }

  Z3_ast key = mk_ast_key(ctx, sort_name_string, 0);
  // Check if already defined, prevent Z3 errors:
  if (Z3_ast_map_contains(ctx, h->enum_sorts, key)) {
    INFO("enumeration sort %s already defined, can't re-define\n", sort_name_string);
    return FALSE;
  }
  else {
    DEBUG("did not find sort %s in enum_sorts map\n", sort_name_string);
  }
  size_t n;
  PL_skip_list(enum_names_list, 0, &n); // gets list length
  DEBUG("Names has length %lu\n", n);
  Z3_symbol *enum_names = malloc(sizeof(Z3_symbol) * n);

  // here we go through the names list and put them in enum_names; see https://www.swi-prolog.org/pldoc/man?section=foreign-read-list
  term_t head = PL_new_term_ref();   // the elements
  term_t tail = PL_copy_term_ref(enum_names_list); // copy (we modify tail)
  int i = 0;
  while( PL_get_list_ex(tail, head, tail) )
    {
      Z3_symbol a = mk_symbol(ctx, head);
      assert(i < n);
      enum_names[i] = a;
      i++;
  }

  Z3_func_decl *enum_consts  = malloc(sizeof(Z3_func_decl) * n);
  Z3_func_decl *enum_testers  = malloc(sizeof(Z3_func_decl) * n);
  Z3_sort s = Z3_mk_enumeration_sort(ctx, sort_name, n, enum_names, enum_consts, enum_testers);

  // NEXT: we should remember the enum_names so that Prolog atoms can be matched to them.
  // less important, the enum_testers can be used to define is_XXX unary predicates.

  // enum_sorts should be in place before the function declarations!?
  DEBUG("Inserting key %s into enum_sorts\n", Z3_ast_to_string(ctx, key));
  Z3_ast_map_insert(ctx, h->enum_sorts, key, (Z3_ast) s);

  for (i = 0; i < n; i++) {
    DEBUG("Registering %d/%ld enum_declaration %s\n", i, n, Z3_func_decl_to_string(ctx, enum_consts[i]));
    register_function_declaration(ctx, h->enum_declarations, enum_names[i], 0, enum_consts[i]);
  }
  DEBUG("enum declarations has size %u\n", Z3_ast_map_size(ctx, h->enum_declarations));
  // The type inference needs to know about this.
  // We reach down and get the declarations from the global, and let that be the initial map when typechecking.

  free(enum_names);
  free(enum_consts);
  free(enum_testers);
  return TRUE;
}

foreign_t remove_declaration(Z3_context ctx, Z3_ast_map map, const char* name_string, const int arity) {

  Z3_ast key = mk_ast_key(ctx, name_string, arity);
  const char * keyname = Z3_ast_to_string(ctx, key);
  // when removing built-in items, like "=", get errors, so not adding them in the first place
  // INFO("made key %s\n", keyname);
  if (!Z3_ast_map_find(ctx, map, key)) {
    ERROR("Key %s not found\n", keyname);
    return FALSE;
  }
  // INFO("Key %s found\n", keyname);
  Z3_ast_map_erase(ctx, map, key);
  return TRUE;
}


foreign_t z3_remove_declaration_foreign(term_t handle_term, term_t name_term, term_t arity_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  int arity;
  char *name_string;
  rval = PL_get_atom_chars(name_term, &name_string);
  if (!rval) return rval;
  rval = PL_get_integer(arity_term, &arity);
  if (!rval) return rval;
  INFO("removing declaration for %s\n", name_string);
  return remove_declaration(h->ctx, h->declarations, name_string, arity);
}

/*
  For debugging:
*/

foreign_t z3_symbol_foreign(term_t handle_term, term_t i, term_t symbol) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  DEBUG("term types: %d %d\n", PL_term_type(i), PL_term_type(symbol));

  Z3_symbol s = mk_symbol(h->ctx, i);
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

foreign_t z3_ast_to_term_foreign(term_t handle_term, term_t ast_term, term_t term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_ast ast;
  rval = PL_get_pointer_ex(ast_term, (void**) &ast);
  if (!rval) {
    return rval;
  }
  return z3_ast_to_term_internal(h->ctx, ast, term);
}


// get a Prolog list with the assertions added to a solver:
// +Solver, -List
foreign_t z3_solver_assertions_foreign(term_t handle_term, term_t list) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_solver solver = h->solver;
  Z3_context ctx = h->ctx;
  Z3_ast_vector v = Z3_solver_get_assertions(ctx, solver);
  Z3_ast_vector_inc_ref(ctx, v);
  int size = Z3_ast_vector_size(ctx, v);
  DEBUG("Vector size is %d\n", size);
  term_t l = PL_new_term_ref();
  PL_put_nil(l);
  for (unsigned i = 0; i < size; ++i) {
    term_t a = PL_new_term_ref(); // putting this outside the loop does not work.
    Z3_ast termi = Z3_ast_vector_get(ctx, v, i);
    z3_ast_to_term_internal(ctx, termi, a);
    int res = PL_cons_list(l, a, l);
    if (!res) {
      Z3_ast_vector_dec_ref(ctx, v);
      return res;
    }
  }
  Z3_ast_vector_dec_ref(ctx, v);
  return PL_unify(l, list);
}


/*
  Converts a Z3 ast to a Prolog term:
  TODO: could make more general.
*/

foreign_t z3_ast_to_term_internal(const Z3_context ctx, Z3_ast ast, term_t term) {
  if (Z3_is_numeral_ast(ctx, ast)) {
    int64_t i;
    if (Z3_get_numeral_int64(ctx, ast, &i)) {
      DEBUG("got numeral %lld\n", i);
      return PL_unify_int64(term, i);
    }
    int64_t num, den;
    if (Z3_get_numeral_rational_int64(ctx, ast, &num, &den)) {
      functor_t div = PL_new_functor(PL_new_atom("/"), 2); // how to construct a Prolog rational in C?
      term_t t = PL_new_term_refs(3);
      term_t t1 = t + 1;
      term_t t2 = t + 2;
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

  if (Z3_get_ast_kind(ctx, ast) == Z3_APP_AST) {
    Z3_app app = Z3_to_app(ctx, ast);
    const unsigned arity = Z3_get_app_num_args(ctx, app);
    DEBUG("We have a Z3_app_ast of arity %d\n", arity);
    term_t subterms = PL_new_term_refs(arity);
    for (int i=0; i<arity; ++i) {
      Z3_ast subterm_ast = Z3_get_app_arg(ctx, app, i);
      if (!z3_ast_to_term_internal(ctx, subterm_ast, subterms+i)) {
        return FALSE;
      }
    }
    Z3_func_decl decl = Z3_get_app_decl(ctx, app);
    Z3_symbol symbol = Z3_get_decl_name(ctx, decl);
    term_t t = PL_new_term_ref();
    functor_t func;
    {
      Z3_string str = Z3_get_symbol_string(ctx, symbol);
      func = PL_new_functor(PL_new_atom(str), arity);
    }
    if (!PL_cons_functor_v(t, func, subterms)) {
      return FALSE;
    }
    return PL_unify(term, t);
  }

  INFO("z3_ast_to_term failed for %s\n", Z3_ast_to_string(ctx, ast));
  return FALSE;
}


foreign_t term_to_z3_ast_foreign(term_t handle_term, term_t formula, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  
  decl_map declaration_map = h->declarations;
  Z3_context ctx = h->ctx;
  Z3_ast z3_ast = term_to_ast(h, declaration_map, formula);
  if (z3_ast == NULL) {
    return FALSE;
  }
  return PL_unify_pointer(result, z3_ast);
}


/*
  For debugging: convert Z3 ast to a Prolog string:
*/

foreign_t z3_ast_string_foreign(term_t handle_term, term_t formula, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_ast z3_form;
  rval = PL_get_pointer(formula, (void **) &z3_form);
  if (!rval) {
    return rval;
  }
  Z3_string rstring = Z3_ast_to_string(h->ctx, z3_form);
  return PL_unify_string_chars(result, rstring);
}

/*
  Does one push on the solver; output is the new number of scopes for the solver.
*/

foreign_t z3_solver_push_foreign(term_t handle_term, term_t output_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  if (!PL_is_variable(output_term)) {
    ERROR("z3_solver_push: output term should be a variable.");
    return FALSE;
  }
  const Z3_solver solver = h->solver;
  const Z3_context ctx = h->ctx;
  Z3_solver_push(ctx, solver);
  unsigned scopes = Z3_solver_get_num_scopes(ctx, solver);

  return PL_unify_uint64(output_term, scopes);
}

/* Pops the solver npops times. Output is the new number of scopes for the solver. */

foreign_t z3_solver_pop_foreign(const term_t handle_term, const term_t npops, term_t output_term) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_solver solver = h->solver;

  int nbacktrack;
  rval = PL_get_integer(npops, &nbacktrack);
  if (!rval) return rval;

  const Z3_context ctx = h->ctx;
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
 Assert formula for solver.
 unsafe: can crash SWI Prolog by putting in a random int as the handle pointer
*/

foreign_t z3_assert_foreign(term_t handle_term, term_t formula) {
  int rval;
  handle h;
  rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  DEBUG("got handle\n");
  Z3_ast z3_formula = term_to_ast(h, h->declarations, formula);
  DEBUG("term_to_ast succeeded\n");

  if (z3_formula == NULL) {
    char *formula_string;
    rval = PL_get_chars(formula, &formula_string, CVT_WRITE);
    if (!rval) {
      ERROR("z3_assert/2: PL_get_chars failed");
      return FALSE;
    }
    // return PL_warning("z3_assert/2: could not make Z3 formula %s", formula_string); // starts the tracer.
    ERROR("z3_assert/2: could not make Z3 formula %s\n", formula_string);
    return FALSE;
  }

  DEBUG("made formula %p\n", (void *) z3_formula);
  Z3_sort formula_sort = Z3_get_sort(h->ctx, z3_formula);
  Z3_sort_kind kind = Z3_get_sort_kind(h->ctx, formula_sort);
  if (kind != Z3_BOOL_SORT) {
    char * formula_string;
    rval = PL_get_chars(formula, &formula_string, CVT_WRITE);
    if (!rval) {
      ERROR("PL_get_chars failed\n");
      return FALSE;
    }
    ERROR("z3_assert/2: cannot assert non-boolean formula %s\n", formula_string);
    // look into PL_raise_exception
    return FALSE;
  }
  DEBUG("checked sort\n");
  DEBUG("Asserting for handle %p, context %p, solver %p\n", h, h->ctx, h->solver);
  
  Z3_solver_assert(h->ctx, h->solver, z3_formula);
  DEBUG("did assert\n");
  return TRUE;
}


foreign_t z3_solver_scopes_foreign(term_t handle_term, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  unsigned scopes = Z3_solver_get_num_scopes(h->ctx, h->solver);
  return PL_unify_uint64(result, scopes);
}

foreign_t z3_check_foreign(term_t handle_term, term_t status_arg) {
  handle h;
  int rval = PL_get_pointer(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_solver solver = h->solver;
  const Z3_context ctx = h->ctx;
  DEBUG("Checking solver %p with context %p\n", solver, ctx);

  Z3_lbool check_status = Z3_solver_check(ctx, solver);
  DEBUG("did check, status %d\n", check_status);
  rval = z3_lbool_to_atom(check_status, status_arg);
  DEBUG("did status to atom %d\n", rval);
  return rval;
}


foreign_t z3_check_and_print_foreign(term_t handle_term, term_t status_arg) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) {
    return rval;
  }
  const Z3_lbool check_status = solver_check_and_print(h->ctx, h->solver);
  return z3_lbool_to_atom(check_status, status_arg);
}


// The function name is the one being declared; subterms are the types, last one is the result.
// We call get_function_declaration to get existing declarations, check if they are compatible with the request.
// We cannot redeclare things from one query to the next, unless we reset the declarations at each query.

// This approach leaves open the possibility of sharing declarations from one query to the next, in a more stateful API.


Z3_func_decl make_function_declaration(handle h, const term_t formula, term_t range_term) {
   atom_t name;
   size_t arity;
   int res;

   Z3_context ctx = h->ctx;
   decl_map declaration_map = h->declarations;

   /*
   char *formula_string;
   res = PL_get_chars(formula, &formula_string, CVT_WRITE);
   if (res) {
     INFO("Argument to make_function_declaration: %s\n", formula_string);
   }
   else {
     INFO("Could not make make_function_declaration formula string\n");
   }
   */

   res = PL_get_name_arity(formula, &name, &arity);
   if (!res || !PL_is_ground(formula)) {
     char *formula_string = NULL;
     if (PL_get_chars(formula, &formula_string, CVT_WRITE)) {
       ERROR("Bad argument to make_function_declaration: %s\n", formula_string);
     }
     return NULL;
   }

   const char *name_string = PL_atom_nchars(name, NULL);
   DEBUG("Making function declaration based on %s/%lu\n", name_string, arity);
   const Z3_symbol symbol = Z3_mk_string_symbol(ctx, name_string);
   Z3_sort *domain = malloc(sizeof(Z3_sort) * arity);
   term_t a = PL_new_term_ref();
   for (int i=1; i<=arity; ++i) {
     int res = PL_get_arg(i, formula, a);
     // DEBUG("Argument %d, res is %d\n", i, res);
     if (!res) {
       ERROR("PL_get_arg in make_function_declaration failed\n");
       free(domain);
       return NULL;
     }

     /*
     char *formula_string;
     if (PL_get_chars(a, &formula_string, CVT_WRITE)) {
        INFO("Calling mk_sort for domain %s\n", formula_string);
      }
     */
     assert(i-1 < arity);
     if (NULL == (domain[i-1] = mk_sort(h, a))) {
       INFO("make_function_declaration returning NULL\n");
       free(domain);
       return NULL;
     }
     DEBUG("Made domain %s\n", Z3_ast_to_string(ctx, (Z3_ast) domain[i-1]));
   }

   Z3_sort range_sort = mk_sort(h, range_term);
   if (range_sort == NULL) {
     ERROR("Got null for range_sort\n");
     char *fchars;
     int res = PL_get_chars(formula, &fchars, CVT_WRITE);
     if (!res) fchars = NULL;
     ERROR("Formula: %s\n", fchars);
     res = PL_get_chars(range_term, &fchars, CVT_WRITE);
     if (!res) fchars = NULL;
     ERROR("Range: %s\n", fchars);
     free(domain);
     return NULL;
   }

   int enum_found = false;

   Z3_func_decl result = get_function_declaration(h->ctx, h->declarations, name_string, arity);
   if (result == NULL) {
     result = get_function_declaration(h->ctx, h->enum_declarations, name_string, arity);
     if (result != NULL) {
       DEBUG("Found existing enum declaration for %s/%ld\n", name_string, arity);
       enum_found = true;
     }
   }
   else {
     DEBUG("Found existing non-enum declaration for %s/%ld\n", name_string, arity);
   }

   if (result == NULL) { // make a new one, register it:
     DEBUG("Could not find any declaration for %s/%ld, making new one\n", name_string, arity);
     result = Z3_mk_func_decl(ctx, symbol, arity, arity == 0 ?  0 : domain, range_sort);
     if (result != NULL) {
       register_function_declaration(h->ctx, h->declarations, symbol, arity, result);
       DEBUG("Z3_mk_func_decl result is %s\n", Z3_ast_to_string(ctx, Z3_func_decl_to_ast(ctx, result)));
     }
   }
   else {
     if (!enum_found) {
       // this catches problems like asserting f(a:int,a:bool):
       Z3_func_decl test =  Z3_mk_func_decl(ctx, symbol, arity, arity == 0 ?  0 : domain, range_sort);
       if (test != result) {
         ERROR("New declaration for \"%s\" is different from old one. Try z3_reset_declarations/1.\n", name_string);
         result = NULL;
         // an alternative is to just let the new declaration overwrite the old one. Combined with the backtrackable typemap, should be safe,
         // but requires everything is declared beforehand, e.g. no direct z3_assert(a:bool).
       }
     }
   }

   free(domain);
   return result;
}



// Makes a function (or constant) declarations.
// Example: z3_declare_function(f(int, bool), int, R).
// Example: z3_declare_function(f(int, int), int, X)

// Note: This does not handle the case where formula is not ground.

foreign_t z3_declare_function_foreign(term_t handle_term, const term_t formula, const term_t range, term_t result) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  atom_t name;

  size_t arity;
  if (PL_is_variable(formula)) {
    ERROR("should not directly declare Z3 types for variables, use attributes instead\n");
    return FALSE;
  }
  int res = PL_get_name_arity(formula, &name, &arity);
  if (!res) {
    char *formula_chars = NULL;
    char *range_chars = NULL;
    res = PL_get_chars(formula, &formula_chars, CVT_WRITE);
    res = PL_get_chars(range, &range_chars, CVT_WRITE);
    ERROR("Bad declaration, term %s and range %s\n", formula_chars, range_chars);
    return FALSE;
  }
  if (!PL_is_ground(formula)) {
    ERROR("z3_declare_function should have ground arguments\n");
    return FALSE;
  }

  Z3_func_decl decl = make_function_declaration(h, formula, range);
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
    Z3_func_interp_inc_ref(ctx, finterp);

    unsigned arity = Z3_func_interp_get_arity(ctx, finterp);
    DEBUG("Arity is %d\n", arity);

    unsigned fentries = Z3_func_interp_get_num_entries (ctx, finterp);
    DEBUG("Entries is %d\n", fentries);
    bool problem = false;
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
        if (!z3_ast_to_term_internal(ctx, keyw, subterms+w)) {
          problem = true;
          break;
        }
      }
      
      if (problem) {
        Z3_func_entry_dec_ref(ctx, point);
        break;
      }

      // NEXT: Use PL_put_dict to make a map directly.
      functor_t func;
      {
        const Z3_string function_name = Z3_get_symbol_string(ctx, symbol);
        DEBUG("Making func using %s\n", function_name);
        func = PL_new_functor(PL_new_atom(function_name), arity);
      }
      if (!PL_cons_functor_v(lhs, func, subterms)) {
        Z3_func_entry_dec_ref(ctx, point);
        problem = true;
        break;
      }

      DEBUG("making rhs\n");
      term_t rhs = PL_new_term_ref();
      if (!z3_ast_to_term_internal(ctx, value, rhs)) {
        Z3_func_entry_dec_ref(ctx, point);
        problem = true;
        break;
      }

      term_t pair = PL_new_term_ref();
      if (!PL_cons_functor(pair, pair_functor, lhs, rhs)) {
        DEBUG("error consing functor\n");
        Z3_func_entry_dec_ref(ctx, point);
        problem = true;
        break;
      }

      DEBUG("consing list\n");
      int r = PL_cons_list(l, pair, l);
      if (!r) {
        Z3_func_entry_dec_ref(ctx, point);
        problem = true;
        break;
      }
      Z3_func_entry_dec_ref(ctx, point);
    }
    
    if (problem) {
      Z3_func_interp_dec_ref(ctx, finterp);
      return FALSE;
    }

    // In a scenario like z3_push(and(f(a:int) = 3, f(a,a) = 4)), z3_model_map(M), z3_check_and_print(R).
    // need to distinguish the two fs.

    // The else terms will be of the form "(f/N-else)-val". This way they can be included in any map/assoc,
    // and can still be distinguished from the other cases, which are of the form "f(x...)-val)".

    DEBUG("getting the else\n");
    Z3_ast felse = Z3_func_interp_get_else(ctx, finterp);
    term_t else_value = PL_new_term_ref();
    if (!z3_ast_to_term_internal(ctx, felse, else_value)) {
      Z3_func_interp_dec_ref(ctx, finterp);
      return FALSE;
    }

    const functor_t slash_functor = PL_new_functor(PL_new_atom("/"), 2);
    term_t top_pair_term = PL_new_term_refs(6);
    term_t else_term = top_pair_term + 1;
    term_t fname_term = top_pair_term + 2;
    term_t arity_term = top_pair_term + 3;
    term_t fname_arity_term = top_pair_term + 4;
    term_t else_singleton = top_pair_term + 5;
    bool ok;
    { // brackets here to make sure function_name is not reused:
      const Z3_string function_name = Z3_get_symbol_string(ctx, symbol);
      ok = PL_put_atom_chars(fname_term, function_name);
    }
    
    ok = ok && PL_put_integer(arity_term, arity);
    // arity term is f/N
    ok = ok && PL_cons_functor(fname_arity_term, slash_functor, fname_term, arity_term);

    // else_term is a pair " F/N-else ":
    ok = ok && PL_put_atom_chars(else_singleton, "else");
    ok = ok && PL_cons_functor(else_term, pair_functor, fname_arity_term, else_singleton);
    // we now make a pair " <else_term> - else_value ":
    ok = ok && PL_cons_functor(top_pair_term, pair_functor, else_term, else_value);
    ok = ok && PL_cons_list(l, top_pair_term, l);
    
    Z3_func_interp_dec_ref(ctx, finterp);
    if (!ok) return FALSE;
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

    term_t lhs = PL_new_term_refs(3);
    term_t rhs = lhs + 1;
    term_t pair = lhs + 2;
    
    int res = PL_put_atom_chars(lhs, constant_name);
    if (!res) {
      ERROR("PL_put_atom_chars failed\n");
      return FALSE;
    }

    DEBUG("making rhs\n");
    if (!z3_ast_to_term_internal(ctx, value, rhs)) {
      return FALSE;
    }

    if (!PL_cons_functor(pair, pair_functor, lhs, rhs)) {
      ERROR("error consing functor\n");
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


foreign_t z3_model_functions_foreign(term_t handle_term, term_t model_term, term_t list) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  const Z3_context ctx = h->ctx;
  Z3_model model;
  rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) return rval;

  Z3_model_inc_ref(ctx, model);
  rval = model_functions(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}

foreign_t z3_model_constants_foreign(term_t handle_term, term_t model_term, term_t list) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;
  Z3_context ctx = h->ctx;
  Z3_model model;
  rval = PL_get_pointer_ex(model_term, (void **) &model);
  if (!rval) return rval;
  Z3_model_inc_ref(ctx, model);
  rval = model_constants(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}

// useful to check validity of handle-related things
foreign_t z3_handle_id_foreign(term_t handle_term, term_t result_term) {
    handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  return PL_unify_int64(result_term, h->handle_id);
}

// Makes a Z3 sort from a Prolog expression:

Z3_sort mk_sort(handle h, term_t expression) {
  Z3_context ctx = h->ctx;
  switch (PL_term_type(expression)) {
  case PL_ATOM: {
    char *name_string;
    int res = PL_get_atom_chars(expression, &name_string);
    if (!res) {
      return NULL;
    }
    DEBUG("making sort for atom %s\n", name_string);
    if (strcmp(name_string, "bool") == 0 || strcmp(name_string, "boolean") == 0) {
      DEBUG("returning bool sort\n");
      return h->bool_sort;
    }
    if (strcmp(name_string, "int") == 0 || strcmp(name_string, "integer") == 0) {
      DEBUG("returning int sort\n");
      return h->int_sort;
    }
    if (strcmp(name_string, "float") == 0 || strcmp(name_string, "real") == 0 || strcmp(name_string, "double") == 0) {
      DEBUG("returning sort for float/real/double\n");
      return h->real_sort; // not the same as a floating point number in Z3
      // return Z3_mk_fpa_sort_double(ctx);
    }
    // Check if there's an enumeration sort for it:
    Z3_ast key = mk_ast_key(ctx, name_string, 0);
    DEBUG("Looking for enum sort declaration for %s, key %s\n", name_string, Z3_ast_to_string(ctx, key));
    if (!Z3_ast_map_contains(ctx, h->enum_sorts, key)) {
      DEBUG("Did not find sort %s in enum_sorts map\n", name_string);
      // will make uninterpreted
    }
    else {
      Z3_sort sort = (Z3_sort) Z3_ast_map_find(ctx, h->enum_sorts, key);
      DEBUG("Found enum sort declaration for %s\n", name_string);
      return sort;
    }

    Z3_symbol uninterpreted_name = Z3_mk_string_symbol(ctx, name_string);
    DEBUG("Making uninterpreted sort for %s\n", name_string);
    return Z3_mk_uninterpreted_sort(ctx, uninterpreted_name);
    break;
  }
  case PL_TERM:
    assert(PL_is_compound(expression));

    char *formula_string = NULL;
    int res = PL_get_chars(expression, &formula_string, CVT_WRITE);
    DEBUG("mk_sort got compound term %s\n", formula_string);

    atom_t name;
    size_t arity;
    res = PL_get_name_arity(expression, &name, &arity);
    if (!res) {
      ERROR("PL_get_name_arity failed\n");
      return FALSE;
    }

    const char *name_string = PL_atom_nchars(name, NULL);
    // INFO("sort expression %s has arity %lu\n", name_string, arity);

    if (strcmp(name_string, "bv")==0) {
      CHECK_ARITY(name_string, 1, arity);
      term_t a = PL_new_term_ref();
      res = PL_get_arg(1, expression, a);
      if (!res) return FALSE;
      int width;
      res = PL_get_integer_ex(a, &width);
      if (!res) return NULL;
      DEBUG("Making bit vector sort of width %d\n", width);
      return Z3_mk_bv_sort(ctx, width);
    }


  /*
    term_t a = PL_new_term_ref();
    Z3_sort *subterms = calloc(arity, sizeof(Z3_sort));
    for (int n=1; n<=arity; n++) {
      res = PL_get_arg(n, expression, a);
      INFO("mk_sort: Argument %d, res is %d\n", n, res);
      if (!res) {
        return FALSE;
      }
      char *formula_string;
      if (PL_get_chars(a, &formula_string, CVT_WRITE)) {
        INFO("Calling mk_sort for subterm %s\n", formula_string);
      }
      subterms[n-1] = mk_sort(ctx, a); // datatypes use constructors, not subsorts.
      if (subterms[n-1] == NULL) {
        return NULL;
      }
    }
    // for bitvectors, subarg is an int.
    ERROR("WARN - need to finish compound case for mk_sort\n");
  */

    return NULL;
    break;
  case PL_VARIABLE: {
    // We'll do this in Prolog, rather than here, so fail:
    ERROR("mk_sort can't take variables\n");
    return NULL;
  }
  default: {
    char *expression_string;
    res = PL_get_chars(expression, &expression_string, CVT_WRITE);
    ERROR("WARN - unimplemented mk_sort for %s\n", expression_string);
    return NULL;
  }
  }
  assert(false); // unreachable
} // mk_sort


/*
  Converts the Prolog term "formula" to a Z3 AST.
  Returns NULL if it fails:
*/

Z3_ast term_to_ast(const handle h, decl_map declaration_map, const term_t formula) {
  const Z3_context ctx = h->ctx;
  long lval;
  Z3_ast result = NULL;
  switch (PL_term_type(formula)) {

  case PL_VARIABLE:
    // It could be nice to look at the attributes, if any, and use them instead of the variable,
    // but the foreign interface does not offer methods for doing so.
    ERROR("Can't call term_to_ast on non-ground terms\n");
    return NULL;

  // ********************************************* atom, string, integer cases ****************************************/
  case PL_ATOM: {
    int bval;
    if (PL_get_bool(formula, &bval)) {
      DEBUG("Got boolean\n");
      if (bval) {
        return Z3_mk_true(ctx);
      }
      return Z3_mk_false(ctx);
    }

    char *atom_string;
    int res = PL_get_atom_chars(formula, &atom_string);
    if (!res) {
      return NULL;
    }
    DEBUG("Got atom %s\n", atom_string);

    Z3_func_decl declaration = get_function_declaration(h->ctx, declaration_map, atom_string, 0);
    if (declaration == NULL) {
      DEBUG("did not find declaration for %s in declaration_map, trying enums\n", atom_string);
      declaration = get_function_declaration(h->ctx, h->enum_declarations, atom_string, 0);
      if (declaration != NULL) {
        DEBUG("Found declaration for %s in enum_declarations\n", atom_string);
      }
    }

    if (declaration == NULL) {
      DEBUG("did not find declaration for %s, defaulting to int\n", atom_string);
    }
    else {
      const Z3_string decstring  = Z3_func_decl_to_string(ctx, declaration);
      DEBUG("Found function %s declaration %s\n", atom_string, decstring);
    }
    if (declaration == NULL) { // Undeclared atoms are by default ints; we could require everything to be declared.
      DEBUG("term_to_ast got atom %s, default int\n", atom_string);
      result = mk_int_var(ctx, atom_string);
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
      Z3_sort INT_SORT = Z3_mk_int_sort(ctx);
      return Z3_mk_int64(ctx, lval, INT_SORT);
    }
    else {
      mpz_t mpz;
      mpz_init(mpz);
      int res = PL_get_mpz(formula, mpz);
      if (!res) {
        ERROR("Could not get long in PL_INTEGER case\n");
      }
      else {
        fprintf(stderr, "Made mpz\n");
      }
      mpz_clear(mpz);
      return NULL;
    }
    break;
  case PL_RATIONAL:
    ERROR("TODO: PL_RATIONAL\n");
    // look at PL_get_mpq
    break;
  case PL_FLOAT: {
    // double myf;
    // We don't use PL_get_float because Z3 does not make reals from floats.
    // Z3_sort sort = Z3_mk_fpa_sort_double(ctx);
    DEBUG("making float\n");
    char *formula_string;
    if (PL_get_chars(formula, &formula_string, CVT_FLOAT) ) {
      result = Z3_mk_numeral(ctx, formula_string, h->real_sort);
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

  // ********************************************* compound term_to_ast case ****************************************/

  case PL_TERM:
    assert(PL_is_compound(formula));
    atom_t name;
    size_t arity;
    int res = PL_get_name_arity(formula, &name, &arity);
    if (!res) {
      return NULL;
    }
    DEBUG("arity is %lu\n", arity);

    const char *name_string = PL_atom_nchars(name, NULL); // PL_atom_chars(name) is deprecated.
    DEBUG("functor name: %s\n", name_string);

    if (strcmp(name_string, ":")==0) { // Path where : is not handled at the Prolog level but given directly to Z3
      // z3.pl now strips all the ":" from the term, so this path is not taken there.
      // we expect symbol:sort
      CHECK_ARITY(name_string, 2, arity);
      term_t name_term = PL_new_term_ref();
      res = PL_get_arg(1, formula, name_term);
      if (!res) {
        ERROR("PL_get_arg 1 failed\n");
        return NULL;
      }
      if (!PL_is_atom(name_term)) {
        char *term_string = NULL;
        int res = PL_get_chars(formula, &term_string, CVT_WRITE);
        if (!res) term_string = NULL;
        ERROR("The C wrapper can only handle atoms on the lhs of \":\", got %s\n", term_string);
        return NULL;
        // To improve this, we would need to infer the function type for the lhs, and compare with the rhs.
        // Better done in z3.pl.
      }
      Z3_symbol symbol_name = mk_symbol(ctx, name_term);
      term_t range = PL_new_term_ref();
      res = PL_get_arg(2, formula, range);
      if (!res) {
        ERROR("PL_get_arg 2 failed\n");
        return NULL;
      }

      /*
        char *formula_string;
        if (PL_get_chars(range, &formula_string, CVT_WRITE) ) {
           INFO("Calling mk_sort for range %s\n", formula_string);
        }
      */

      Z3_sort sort = mk_sort(h, range);
      if (sort == NULL) {
        INFO("mk_sort for symbol is null\n");
        return NULL;
      }
      // We are converting PL to Z3. We call make_function_declaration
      // to catch inconsistent uses of the same constant.
      atom_t name_atom;
      res = PL_get_atom(name_term, &name_atom);
      DEBUG("Declaring for %s\n", name_string);
      // If we overwrote function declarations here, then could do z3_assert(a:int, a:bool), which we don't want.
      Z3_func_decl decl = make_function_declaration(h, name_term, range);
      if (decl == NULL) {
        ERROR("Failed making decl\n");
        return NULL;
      }
      DEBUG("making const\n");
      result = Z3_mk_const(ctx, symbol_name, sort);
      DEBUG("making const result is %s\n", Z3_ast_to_string(ctx, result));
      return result;
    } // end ":" case

    // See also prolog's getbit/2.
    // replace by int2bv, have bv_numeral take a list of bools?

    if (strcmp(name_string, "bv_numeral")==0) {
      CHECK_ARITY(name_string, 1, arity); // a list of booleans
      term_t list_term = PL_new_term_ref();
      res = PL_get_arg(1, formula, list_term);
      if (!PL_is_list(list_term)) {
        ERROR("Argument to bv_numeral should be a list of booleans");
        return NULL;
      }
      size_t width;
      PL_skip_list(list_term, 0, &width); // gets list length
      bool * bits = malloc(width * sizeof(bool));
      term_t head = PL_new_term_ref();   // the elements
      term_t tail = PL_copy_term_ref(list_term); // copy (we modify tail)
      int rc = TRUE;
      int i = 0;
      while( rc && PL_get_list_ex(tail, head, tail) )
        {
          int b;
          rc = PL_get_bool_ex(head, &b);
          if (rc) {
            assert(i < width);
            bits[i] = b;
            i++;
          }
        }
      
      result = Z3_mk_bv_numeral(ctx, width, bits);
      free(bits);
      return result;
    }

    // TODO: special cases for mk_numeral and mk_unsigned_int64. Both use an int and a sort as an argument.
    // we don't do unsigned_int because PL does not have it, could be confusing.

    if (strcmp(name_string, MK_NUMERAL)==0 ||
        strcmp(name_string, "mk_unsigned_int64")==0) { // confusing name, makes something of the specified sort.
      // get sort from second argument:
      DEBUG("numeral/unsigned_int64 case\n");
      term_t sort_term = PL_new_term_ref();
      res = PL_get_arg(2, formula, sort_term);
      if (!res) return NULL;
      Z3_sort sort = mk_sort(h, sort_term);
      term_t arg_term = PL_new_term_ref();
      res = PL_get_arg(1, formula, arg_term);
      if (!res) return NULL;
      if (strcmp(name_string, MK_NUMERAL)==0) {
        char *numeral_string;
        size_t len;
        res = PL_get_string_chars(arg_term, &numeral_string, &len);
        if (!res) return NULL;
        result = Z3_mk_numeral(ctx, numeral_string, sort);
        return result;
      }
      else { // unsigned_int case:
          uint64_t uint;
          res = PL_get_uint64(arg_term, &uint);
          return Z3_mk_unsigned_int(ctx, uint, sort);
        }
    }
    
    // special case because of the bool arg:
    if (strcmp(name_string, "bv2int")==0) {
      CHECK_ARITY(name_string, 2, arity);
      term_t sub1 = PL_new_term_refs(2);
      term_t sub2 = sub1 + 1;
      res = PL_get_arg(1, formula, sub1);
      res = PL_get_arg(2, formula, sub2);
      int is_signed;
      if (!PL_get_bool(sub2, &is_signed)) {
        ERROR("Second argument to bv2int should be boolean");
        return NULL;
      }
      Z3_ast arg = term_to_ast(h, declaration_map, sub1);
      result = Z3_mk_bv2int(ctx, arg, is_signed);
      return result;
    }

    if (strcmp(name_string, "int2bv")==0) {
      CHECK_ARITY(name_string, 2, arity);
      term_t sub1 = PL_new_term_refs(2);
      term_t sub2 = sub1 + 1;
      res = PL_get_arg(1, formula, sub1);
      res = PL_get_arg(2, formula, sub2);
      int width;
      if (!PL_get_integer(sub1, &width)) {
        ERROR("First argument to int2bv should be an integer");
        return NULL;
      }
      Z3_ast arg = term_to_ast(h, declaration_map, sub2);
      result = Z3_mk_int2bv(ctx, width, arg);
      return result;
    }

    if (strcmp(name_string, "bvadd_no_overflow")==0
      || strcmp(name_string, "bvmul_no_overflow") == 0
      || strcmp(name_string, "bvsub_no_underflow") == 0) {
      CHECK_ARITY(name_string, 3, arity);
      term_t sub1 = PL_new_term_refs(3);
      term_t sub2 = sub1 + 1;
      term_t sub3 = sub1 + 2;
      res = PL_get_arg(1, formula, sub1);
      res = PL_get_arg(2, formula, sub2);
      res = PL_get_arg(3, formula, sub3);
      int is_signed;
      if (!PL_get_bool(sub3, &is_signed)) {
        ERROR("Third argument to %s should be boolean", name_string);
        return NULL;
      }
      Z3_ast arg1 = term_to_ast(h, declaration_map, sub1);
      Z3_ast arg2 = term_to_ast(h, declaration_map, sub2);

      if (strcmp(name_string, "bvadd_no_overflow") == 0) {
        return Z3_mk_bvadd_no_overflow(ctx, arg1, arg2, is_signed);
      }
      else if (strcmp(name_string, "bvmul_no_overflow") == 0) {
        return Z3_mk_bvmul_no_overflow(ctx, arg1, arg2, is_signed);
      }
      else {
        assert(strcmp(name_string, "bvsub_no_underflow") == 0);
        return Z3_mk_bvsub_no_underflow(ctx, arg1, arg2, is_signed);
      }
      assert(false); // unreachable
    }



    // *************************** End special cases ********************/


    // *************************** Recursive call on subterms ***********/

    term_t a = PL_new_term_ref();
    Z3_ast *subterms = calloc(arity, sizeof(Z3_ast));
    for (int n=1; n<=arity; ++n) {
      res = PL_get_arg(n, formula, a);
      DEBUG("term_to_ast: Argument %d, res is %d\n", n, res);
      assert(res);
      subterms[n-1] = term_to_ast(h, declaration_map, a); // Recursive call
      if (subterms[n-1] == NULL) {
        DEBUG("Making subterm %d failed\n", n);
        free(subterms);
        return NULL;
      }
      DEBUG("Made subterm %d, %s\n", n, Z3_ast_to_string(ctx, subterms[n-1]));
    }

    // ********************************************* built-in compound term_to_ast  ****************************************/

    if (strcmp(name_string, "+") == 0 ) {
      result = Z3_mk_add(ctx, arity, subterms);
    }
    else if (strcmp(name_string, "*") == 0 ) {
      result = Z3_mk_mul(ctx, arity, subterms);
    }
    else if (strcmp(name_string, "-") == 0 || strcmp(name_string, "minus") == 0 ) {
      if (arity == 1) {
        result = Z3_mk_unary_minus(ctx, subterms[0]);
      }
      else {
        // we allow arities > 2
        result = Z3_mk_sub(ctx, arity, subterms);
      }
    }
    else if (strcmp(name_string, "div") == 0 || strcmp(name_string, "/") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      DEBUG("making div\n");
      result = Z3_mk_div(ctx, subterms[0], subterms[1]);
      // The arguments must either both have int type or both have real type.
      // division by 0 is allowed, can be anything
      DEBUG("result is %s\n", Z3_ast_to_string(ctx, result));
    }
    else if (strcmp(name_string, "mod") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_mod(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "rem") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_rem(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "power") == 0 || strcmp(name_string, "**") == 0 || strcmp(name_string, "^") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_power(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "<") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_lt(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "=<") == 0 || strcmp(name_string, "leq") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_le(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, ">") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_gt(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, ">=") == 0 || strcmp(name_string, "geq") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_ge(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "is_int") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_is_int(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "int2real") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_int2real(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "real2int") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_real2int(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "=") == 0 || strcmp(name_string, "==") == 0 || strcmp(name_string, "equals") == 0 ) {
      DEBUG("making equals\n");
      CHECK_ARITY(name_string, 2, arity);
      // Check that types are compatible; otherwise Z3 quits/crashes
      Z3_sort s1 = Z3_get_sort(ctx, subterms[0]);
      Z3_sort s2 = Z3_get_sort(ctx, subterms[1]);
      if ((!numeric_sort(ctx, s1)) && (!numeric_sort(ctx, s2)) && (s1 != s2)) // equalities between some expressions of numeric sorts seem to be OK for Z3:
        {
          ERROR("different types for equals, failing\n");
          ERROR("sort1: %s\n", Z3_sort_to_string(ctx, s1)); // as with ast_to_string, one sort_to_string invaliates the previous one, so we use two statements.
          ERROR("sort2: %s\n", Z3_sort_to_string(ctx, s2));
          // ERROR("sort kinds: %u and %u\n", Z3_get_sort_kind(ctx, s1), Z3_get_sort_kind(ctx, s2));
          return NULL;
      }
      DEBUG("making equals\n");
      result = Z3_mk_eq(ctx, subterms[0], subterms[1]);
      DEBUG("made equals\n");
    }
    else if (strcmp(name_string, "distinct") == 0 ) {
      result = Z3_mk_distinct(ctx, arity, subterms);
    }
    else if (strcmp(name_string, "divides") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_divides(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "not") == 0 ) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_not(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "ite") == 0 ) {
      CHECK_ARITY(name_string, 3, arity);
      result = Z3_mk_ite(ctx, subterms[0], subterms[1], subterms[2]);
    }
    else if (strcmp(name_string, "iff") == 0 || strcmp(name_string, "<=>") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_iff(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "implies") == 0 || strcmp(name_string, "->") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_implies(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "xor") == 0 ) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_xor(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "<>") == 0 ) {
      CHECK_ARITY(name_string, 2, arity);
      Z3_sort s1 = Z3_get_sort(ctx, subterms[0]);
      Z3_sort s2 = Z3_get_sort(ctx, subterms[1]);
      if (numeric_sort(ctx, s1) && numeric_sort(ctx, s2) && (s1 != s2)) { // for numeric types, translate to (a<b or a>b)
        Z3_ast dis1 = Z3_mk_lt(ctx, subterms[0], subterms[1]);
        Z3_ast dis2 = Z3_mk_gt(ctx, subterms[0], subterms[1]);
        if (dis1 == NULL || dis2 == NULL) return(NULL);
        Z3_ast disjuncts[2] = {dis1, dis2};
        return Z3_mk_or(ctx, 2, disjuncts);
      }
      Z3_ast equality = Z3_mk_eq(ctx, subterms[0], subterms[1]);
      if (NULL == equality) {
        ERROR("incompatible types for <>\n");
        ERROR("sort1: %s\n", Z3_sort_to_string(ctx, s1));
        ERROR("sort2: %s\n", Z3_sort_to_string(ctx, s2));
        result = NULL;
      }
      else {
        result = Z3_mk_not(ctx, equality);
      }
    }
    // between, inclusive (as in python):
    else if (strcmp(name_string, "between") == 0) {
      CHECK_ARITY(name_string, 3, arity);
      Z3_ast conj1 = Z3_mk_ge(ctx, subterms[0], subterms[1]);
      Z3_ast conj2 = Z3_mk_le(ctx, subterms[0], subterms[2]);
      if (conj1 == NULL || conj2 == NULL) return(NULL);
      Z3_ast conjuncts[2] = {conj1, conj2};
      return Z3_mk_and(ctx, 2, conjuncts);
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



    // ********************************************* bit vectors ************************************/
    // in order of appearance in https://z3prover.github.io/api/html/z3__api_8h.html

    else if (strcmp(name_string, "bvadd") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvadd(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvadd_no_underflow") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvadd_no_underflow(ctx, subterms[0], subterms[1]);
    }

    /***
        special cases because of the extra arg:
        (strcmp(name_string, "bvadd_no_overflow") == 0)
        (strcmp(name_string, "bvmul_no_overflow") == 0)
        (strcmp(name_string, "bvsub_no_underflow") == 0)
    ***/

    else if (strcmp(name_string, "bvand") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvand(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvashr") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvashr(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvlshr") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvlshr(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvmul") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvmul(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvmul_no_underflow") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvmul_no_underflow(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvnand") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvand(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvneg") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_bvneg(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "bvneg_no_overflow") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_bvneg_no_overflow(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "bvnor") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvnor(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvnot") == 0) { // bitwise negation
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_bvnot(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "bvor") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvor(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvredand") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_bvredand(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "bvredor") == 0) {
      CHECK_ARITY(name_string, 1, arity);
      result = Z3_mk_bvredor(ctx, subterms[0]);
    }
    else if (strcmp(name_string, "bvsdiv") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsdiv(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsdiv_no_overflow") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsdiv_no_overflow(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsge") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsge(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsgt") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsgt(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvshl") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvshl(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsle") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsle(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvslt") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvslt(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsmod") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsmod(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsrem") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsrem(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsub") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsub(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvsub_no_overflow") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvsub_no_overflow(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvudiv") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvudiv(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvuge") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvuge(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvugt") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvugt(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvule") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvule(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvult") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvult(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvurem") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvurem(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvxnor") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvxnor(ctx, subterms[0], subterms[1]);
    }
    else if (strcmp(name_string, "bvxor") == 0) {
      CHECK_ARITY(name_string, 2, arity);
      result = Z3_mk_bvxor(ctx, subterms[0], subterms[1]);
    }


    // ********************************************* uninterpreted compound term_to_ast  ****************************************/
    else { // uninterpreted function
      DEBUG("Making uninterpreted function declaration for %s\n", name_string);
      // no need to look in enum map because we have a compound term:
      assert(arity > 0);
      Z3_func_decl declaration = get_function_declaration(h->ctx, declaration_map, name_string, arity);
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
    if (! PL_get_chars(formula, &formula_string, CVT_WRITE)) {
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

// +Term, -Term.
foreign_t z3_simplify_term_foreign(term_t handle_term, term_t tin, term_t tout) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  Z3_context ctx = h->ctx;
  decl_map declaration_map = h->declarations;

  Z3_ast ast_in = term_to_ast(h, declaration_map, tin);
  if (ast_in == NULL) {
    return FALSE;
  }
  Z3_ast ast_out = Z3_simplify(ctx, ast_in);
  if (ast_out == NULL) {
    return FALSE;
  }
  return z3_ast_to_term_internal(ctx, ast_out, tout);
}

// make sure that AST maps work:
foreign_t map_test_foreign(term_t handle_term, term_t string_atom) {
  handle h;
  int rval = PL_get_pointer_ex(handle_term, (void **) &h);
  if (!rval) return rval;

  if (!PL_is_atom(string_atom)) return FALSE;
  char *name_string;
  rval = PL_get_atom_chars(string_atom, &name_string);
  if (!rval) return rval;
  
  Z3_context ctx = h->ctx;
  decl_map mymap = Z3_mk_ast_map(ctx);

  int arity = 1;
  Z3_ast key = mk_ast_key(ctx, name_string, arity);

  Z3_ast_map_insert(ctx, mymap, key, key);
  if (Z3_ast_map_contains(ctx, mymap, key)) {
    INFO("found key\n");
  }
  else {
    INFO("did not find key\n");
  }
  Z3_ast key1 = mk_ast_key(ctx, "bar", arity);
  if (Z3_ast_map_contains(ctx, mymap, key1)) {
    INFO("found key1\n");
  }
  else {
    INFO("did not find key1\n");
  }
  // "invalid argument" is reported if we try to remove something that's not there.
  if (!remove_declaration(ctx, mymap, name_string, arity)) {
    ERROR("remove_declaration failed\n");
    return FALSE;
  }
  else {
    INFO("remove worked for %s\n", name_string);
  }

  return TRUE;
}


foreign_t z3_alloc_bytes_foreign(term_t size_term) {
  uint64_t s = Z3_get_estimated_alloc_size();
  return PL_unify_uint64(size_term, s);
}


#define PRED(name, arity, func, attr) \
  PL_register_foreign_in_module("z3_swi_foreign", name, arity, func, attr)

install_t install()
{
  fprintf(stderr, "Installing Z3 package\n");
  
  Z3_string version = Z3_get_full_version();
  fprintf(stderr, "Using Z3 version %s\n", version);

  // name, arity, function, flags

  pair_functor = PL_new_functor(PL_new_atom("="), 2);
  declaration_pair_functor = PL_new_functor(PL_new_atom(":"), 2);

  // make a new solver:
  // hide inside handle:
  // PRED("z3_make_solver", 2, z3_make_solver_foreign, 0); // +handle, -solver
  // PRED("z3_free_solver", 1, z3_free_solver_foreign, 0); // +solver

  PRED("z3_assert", 2, z3_assert_foreign, 0); // +handle, +formula

  // for debugging and unit tests, testing round-trips between Prolog and Z3:
  PRED("term_to_z3_ast", 3, term_to_z3_ast_foreign, 0); // +handle, +formula, -z3_ast_pointer
  PRED("z3_ast_string", 3, z3_ast_string_foreign, 0); // +handle, +formula, -string
  PRED("z3_ast_to_term", 3, z3_ast_to_term_foreign, 0); // +handle, +ast, -formula
  PRED("z3_symbol", 3, z3_symbol_foreign, 0); // +handle, +formula, -symbol_pointer

  PRED("z3_declare_function", 4, z3_declare_function_foreign, 0); // +handle_term, +pl_term, +range_atom, -declaration_pointer
  PRED("z3_declare_enum", 3, z3_declare_enum_foreign, 0);

  PRED("z3_solver_push", 2, z3_solver_push_foreign, 0); // +handle, -num_scopes
  PRED("z3_solver_pop", 3, z3_solver_pop_foreign, 0); // +handle, +numpops, -num_scopes

  PRED("z3_solver_scopes", 2, z3_solver_scopes_foreign, 0); // +handle, -num_scopes):
  PRED("z3_check", 2, z3_check_foreign, 0); // +handle, -status
  PRED("z3_check_and_print", 2, z3_check_and_print_foreign, 0); // +handle, -status

  PRED("z3_get_model", 2, z3_get_model_foreign, 0); // +handle, -model_pointer
  PRED("z3_model_eval", 5, z3_model_eval_foreign, 0); // +handle, +model_pointer, +formula, +completion_flag, -value
  PRED("z3_free_model", 2, z3_free_model_foreign, 0); // +handle, +model

  PRED("z3_simplify_term", 2, z3_simplify_term_foreign, 0); // +term, -simplified_term
  PRED("z3_solver_assertions", 2, z3_solver_assertions_foreign, 0); // +handle_pointer, -assertion_list

  PRED("z3_model_functions", 3, z3_model_functions_foreign, 0); // +handle, +model_pointer, -functions_term
  PRED("z3_model_constants", 3, z3_model_constants_foreign, 0); // +handle, +model_pointer, -constants_term

  // PRED("z3_reset_handle", 1, z3_reset_handle_foreign, 0); // clears everything, use sparingly; but is the only way to reset enums

  PRED("z3_reset_declarations", 1, z3_reset_declarations_foreign, 0); // +handle // clears declarations, including enums, keeps Z3 context
  PRED("z3_get_enum_declarations", 2, z3_get_enum_declarations_foreign, 0); // +handle, -term
  PRED("z3_get_declarations", 2, z3_get_declarations_foreign, 0); // +handle, -term

  // for debugging:
  PRED("z3_declarations_string", 2, z3_declarations_string_foreign, 0); // -string
  PRED("z3_enums_string", 2, z3_enums_string_foreign, 0); // -string

  PRED("z3_remove_declaration", 3, z3_remove_declaration_foreign, 0); // +handle, +name, +arity

  PRED("z3_handle_id", 2, z3_handle_id_foreign, 0); // -context id
  PRED("map_test", 1, map_test_foreign, 0); //

  PRED("z3_new_handle", 1, z3_new_handle_foreign, 0); // -handle
  PRED("z3_free_handle", 1, z3_free_handle_foreign, 0); // +handle

  PRED("z3_alloc_bytes", 1, z3_alloc_bytes_foreign, 0); // +size
  PRED("z3_finalize_memory", 0, z3_finalize_memory_foreign, 0); // +size // debugging only, dangerous.

  PRED("handle_stats", 4, handle_stats_foreign, 0); // +handle, -A, -B, -C
  
}
