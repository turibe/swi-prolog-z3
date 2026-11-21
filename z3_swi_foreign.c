
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdatomic.h>
#include <pthread.h>
#include <time.h>

// /opt/homebrew/Cellar/gmp/6.3.0/include/gmp.h
// #include <gmp.h>
#include <SWI-Stream.h>
#include <SWI-Prolog.h>

#include <z3.h>

/****

     This is a C foreign interface between SWI Prolog and the Z3 prover. It exposes the basic Z3 functionality
     as Prolog predicates, leaving the implementation of more complex applications to Prolog code and libraries.

     The main decision is how to handle Z3 state: context, declarations and solvers.

     It seems nice to embed all the function declarations in the context object.
     For this, we define a "HandleStruct" object that has the Z3 context, plus all the Z3 function declarations.

     This includes enums and enum sorts. However, note that while normal declarations can be reset without having
     to create a new context, enums can't be reset without resetting the context too.

     We now dynamically allocate HandleStruct objects, for greater flexibility at the app level.
     The solver is bundled in the handler. They could be separated, but this would be more error-prone at the Prolog level.

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

// Sorts Z3 accepts in arithmetic comparisons such as <; Bool is converted with (ite b 1 0).
bool numeric_sort(Z3_context ctx, Z3_sort s) {
  Z3_sort_kind k = Z3_get_sort_kind(ctx, s);
  return (k == Z3_BOOL_SORT || k == Z3_INT_SORT || k == Z3_REAL_SORT);
}

// Sorts Z3 lets mix in an equality: Int and Real only (Bool = Int is a sort error).
bool arith_sort(Z3_context ctx, Z3_sort s) {
  Z3_sort_kind k = Z3_get_sort_kind(ctx, s);
  return (k == Z3_INT_SORT || k == Z3_REAL_SORT);
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


static atomic_long handle_counter = 0;

// The HandleStruct has the objects needed to typecheck and convert Prolog terms to Z3.
// Solver and Model objects are separate, and we can do push and pop on solvers from Prolog.

/*
  Handles and models are given to Prolog as blobs (see z3_handle_blob and z3_model_blob below),
  so a freed, garbage-collected, or made-up handle cannot crash the process.

  Lifetime: the HandleStruct is reference counted. The handle blob holds one reference, and each
  live model blob holds one. The Z3 context is deleted when z3_free_handle/1 is called or the handle
  blob is garbage collected, whichever comes first; ctx is then NULL. The struct itself is freed when
  the last reference goes away.

  Model blobs may be garbage collected in SWI-Prolog's gc thread, while another thread is using the
  context. Z3 contexts are not thread-safe, so the release hook does not call Z3. It queues the model
  on pending_models instead, and the next call that uses the handle releases it.

  Threads: a handle may be shared between Prolog threads. Every predicate that takes a handle holds
  h->lock for its whole run (see lock_handle and the *_locked functions), so calls on one handle are
  serialized; calls on different handles run in parallel. A thread waiting for the lock still handles
  Prolog signals (see wait_for_handle_lock), so a time limit, thread_signal/2 or Ctrl-C reaches it.
  The call holding the lock cannot be interrupted that way: a running z3_check, for example, only
  sees signals after Z3 returns.
  Lock order: h->lock before h->pending_lock. Blob release hooks only take pending_lock.
*/

struct HandleStruct {
  Z3_context ctx; // NULL once the context has been deleted
  Z3_solver solver;
  sort_map enum_sorts;  // map from names to Z3 enumeration sorts, used for building terms
  decl_map enum_declarations; // declarations that typechecker will need
  decl_map declarations; // standard declarations
  long handle_id; // used as a unique ID for the context
  Z3_sort int_sort, bool_sort, real_sort;

  pthread_mutex_t lock;          // held for the whole of any predicate that uses this handle
  atomic_int refcount;           // handle blob + one per live model blob
  pthread_mutex_t pending_lock;  // protects ctx becoming NULL and the pending_models list
  Z3_model *pending_models;      // models garbage collected but not yet released in Z3
  size_t num_pending, max_pending;
};

typedef struct HandleStruct *handle;

struct ModelStruct {
  Z3_model model; // NULL once freed
  handle h;       // NULL once freed
};

typedef struct ModelStruct *model_ref;

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
  fprintf(stderr, "Z3 ERROR: code %d %s\n", (int) e, msg);
}

void initialize_handle(handle handle) {
  DEBUG("Initializing handle %p\n", handle);

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

}

// ***************************** HANDLE AND MODEL BLOBS ********************************************

// Drops one reference to h, freeing the struct when it was the last one. The context must already be deleted.
static void handle_release_ref(handle h) {
  if (atomic_fetch_sub(&h->refcount, 1) == 1) {
    assert(h->ctx == NULL);
    pthread_mutex_destroy(&h->lock);
    pthread_mutex_destroy(&h->pending_lock);
    free(h->pending_models);
    free(h);
  }
}

// Releases the models queued by release_model_blob. The caller must hold h->lock, with h->ctx alive.
static void drain_pending_models(handle h) {
  pthread_mutex_lock(&h->pending_lock);
  for (size_t i = 0; i < h->num_pending; i++) {
    Z3_model_dec_ref(h->ctx, h->pending_models[i]);
  }
  h->num_pending = 0;
  pthread_mutex_unlock(&h->pending_lock);
}

// Deletes the Z3 context and everything in it. Safe to call more than once.
// The caller must hold h->lock, or be the blob release hook (when no other thread can be using h).
static void destroy_context(handle h) {
  pthread_mutex_lock(&h->pending_lock);
  if (h->ctx != NULL) {
    h->num_pending = 0; // Z3_del_context frees these models too
    free_handle_contents(h);
    h->ctx = NULL;
  }
  pthread_mutex_unlock(&h->pending_lock);
}

static int release_handle_blob(atom_t a) {
  handle h = PL_blob_data(a, NULL, NULL);
  DEBUG("Garbage collecting handle %ld\n", h->handle_id);
  destroy_context(h);
  handle_release_ref(h);
  return TRUE;
}

static int write_handle_blob(IOSTREAM *s, atom_t a, int flags) {
  (void) flags;
  handle h = PL_blob_data(a, NULL, NULL);
  Sfprintf(s, "<z3_handle>(%ld%s)", h->handle_id, h->ctx == NULL ? ",freed" : "");
  return TRUE;
}

static int release_model_blob(atom_t a) {
  model_ref m = PL_blob_data(a, NULL, NULL);
  handle h = m->h;
  if (h != NULL) {
    pthread_mutex_lock(&h->pending_lock);
    if (h->ctx != NULL && m->model != NULL) {
      if (h->num_pending == h->max_pending) {
        size_t new_max = h->max_pending == 0 ? 8 : 2 * h->max_pending;
        Z3_model *grown = realloc(h->pending_models, new_max * sizeof(Z3_model));
        if (grown == NULL) {
          pthread_mutex_unlock(&h->pending_lock);
          return FALSE; // keep the blob; nothing else to do safely
        }
        h->pending_models = grown;
        h->max_pending = new_max;
      }
      h->pending_models[h->num_pending++] = m->model;
    }
    pthread_mutex_unlock(&h->pending_lock);
    handle_release_ref(h);
  }
  free(m);
  return TRUE;
}

static int write_model_blob(IOSTREAM *s, atom_t a, int flags) {
  (void) flags;
  model_ref m = PL_blob_data(a, NULL, NULL);
  if (m->h == NULL) {
    Sfprintf(s, "<z3_model>(%p,freed)", (void *) m);
  }
  else {
    Sfprintf(s, "<z3_model>(%p,handle=%ld)", (void *) m, m->h->handle_id);
  }
  return TRUE;
}

static PL_blob_t z3_handle_blob = {
  .magic = PL_BLOB_MAGIC,
  .flags = PL_BLOB_NOCOPY,
  .name = "z3_handle",
  .release = release_handle_blob,
  .write = write_handle_blob,
};

static PL_blob_t z3_model_blob = {
  .magic = PL_BLOB_MAGIC,
  .flags = PL_BLOB_NOCOPY,
  .name = "z3_model",
  .release = release_model_blob,
  .write = write_model_blob,
};

/*
  Locks h->lock. While another thread holds it, polls instead of blocking, handling Prolog signals
  between attempts, so a waiting thread can still be interrupted. Returns FALSE, without the lock,
  if a signal handler raised an exception (time_limit_exceeded, for example); the caller returns
  FALSE so the exception propagates. The poll interval starts at 0.1 ms and doubles up to 10 ms.
  (macOS has no pthread_mutex_timedlock, hence trylock and a sleep.)
*/
static int wait_for_handle_lock(handle h) {
  if (pthread_mutex_trylock(&h->lock) == 0) return TRUE; // the usual, uncontended case
  struct timespec delay = { 0, 100000 };
  for (;;) {
    if (PL_handle_signals() < 0) return FALSE;
    nanosleep(&delay, NULL);
    if (pthread_mutex_trylock(&h->lock) == 0) return TRUE;
    if (delay.tv_nsec < 10000000) delay.tv_nsec *= 2;
  }
}

/*
  Gets a live handle from a Prolog term and locks it; the caller must call unlock_handle(h) after.
  Raises instantiation_error, type_error(z3_handle, T), or existence_error(z3_handle, T) for a
  handle whose context has been freed (nothing is locked in those cases).
*/
static int lock_handle(term_t t, handle *hp) {
  void *data;
  PL_blob_t *type;
  if (!PL_get_blob(t, &data, NULL, &type) || type != &z3_handle_blob) {
    if (PL_is_variable(t)) return PL_instantiation_error(t);
    return PL_type_error("z3_handle", t);
  }
  handle h = data; // the term keeps the blob, and so h, alive for the whole call
  if (!wait_for_handle_lock(h)) return FALSE;
  if (h->ctx == NULL) {
    pthread_mutex_unlock(&h->lock);
    return PL_existence_error("z3_handle", t);
  }
  drain_pending_models(h);
  *hp = h;
  return TRUE;
}

static void unlock_handle(handle h) {
  pthread_mutex_unlock(&h->lock);
}

/*
  Gets a live model belonging to h. Raises instantiation_error, type_error(z3_model, T),
  existence_error(z3_model, T) for a freed model, or permission_error(access, z3_model, T)
  for a model that belongs to a different handle.
*/
static int get_model_ref(term_t t, handle h, model_ref *mp) {
  void *data;
  PL_blob_t *type;
  if (!PL_get_blob(t, &data, NULL, &type) || type != &z3_model_blob) {
    if (PL_is_variable(t)) return PL_instantiation_error(t);
    return PL_type_error("z3_model", t);
  }
  model_ref m = data;
  if (m->model == NULL) {
    return PL_existence_error("z3_model", t);
  }
  if (m->h != h) {
    return PL_permission_error("access", "z3_model", t);
  }
  *mp = m;
  return TRUE;
}

static int get_model(term_t t, handle h, Z3_model *model) {
  model_ref m;
  if (!get_model_ref(t, h, &m)) return FALSE;
  *model = m->model;
  return TRUE;
}

/*
  AST and symbol blobs, used by the debugging predicates (term_to_z3_ast/3, z3_ast_to_term/3,
  z3_ast_string/3, z3_symbol/3) and for the declaration returned by z3_declare_function/4.

  The handle's context is created with Z3_mk_context (not Z3_mk_context_rc), which keeps every AST it
  creates until the context is deleted, so these need no Z3 reference counting. A blob only has to keep
  its handle's struct alive, and be used with that handle: once lock_handle has checked the handle is
  live, an object belonging to it is valid.

  The blob data is copied (no PL_BLOB_NOCOPY) and unique, so the same object for the same handle is
  always the same atom; for example, z3_symbol(H, a, S1), z3_symbol(H, a, S2) gives S1 == S2.
  Because a unique blob can be found again instead of created, the handle reference is taken in the
  acquire hook, which runs once per new atom, rather than when the blob is put.
*/

struct ObjStruct {
  void *ptr; // a Z3_ast (also used for function declarations) or a Z3_symbol
  handle h;
};

static void acquire_obj_blob(atom_t a) {
  struct ObjStruct *o = PL_blob_data(a, NULL, NULL);
  atomic_fetch_add(&o->h->refcount, 1);
}

static int release_obj_blob(atom_t a) {
  struct ObjStruct *o = PL_blob_data(a, NULL, NULL);
  handle_release_ref(o->h);
  return TRUE;
}

static int write_obj_blob(IOSTREAM *s, atom_t a, int flags) {
  (void) flags;
  PL_blob_t *type;
  struct ObjStruct *o = PL_blob_data(a, NULL, &type);
  // Printing the AST itself would need the handle's lock, which the write hook cannot take safely.
  Sfprintf(s, "<%s>(%p,handle=%ld)", type->name, o->ptr, o->h->handle_id);
  return TRUE;
}

static PL_blob_t z3_ast_blob = {
  .magic = PL_BLOB_MAGIC,
  .flags = PL_BLOB_UNIQUE,
  .name = "z3_ast",
  .acquire = acquire_obj_blob,
  .release = release_obj_blob,
  .write = write_obj_blob,
};

static PL_blob_t z3_symbol_blob = {
  .magic = PL_BLOB_MAGIC,
  .flags = PL_BLOB_UNIQUE,
  .name = "z3_symbol",
  .acquire = acquire_obj_blob,
  .release = release_obj_blob,
  .write = write_obj_blob,
};

// Unifies t with the blob of the given type for ptr, which belongs to h. The caller holds h->lock.
static int unify_obj(term_t t, PL_blob_t *type, handle h, void *ptr) {
  struct ObjStruct o;
  memset(&o, 0, sizeof(o)); // the bytes are compared for uniqueness
  o.ptr = ptr;
  o.h = h;
  // PL_unify_blob, not PL_put_blob: PL_put_blob's return value says whether the blob is new
  // (which for a unique blob is not an error), not whether it succeeded.
  return PL_unify_blob(t, &o, sizeof(o), type);
}

/*
  Gets the object in a blob of the given type, which must belong to h (already locked and live).
  Raises instantiation_error, type_error(TypeName, T), or permission_error(access, TypeName, T)
  for an object of another handle.
*/
static int get_obj(term_t t, PL_blob_t *type, handle h, void **ptr) {
  void *data;
  PL_blob_t *actual;
  if (!PL_get_blob(t, &data, NULL, &actual) || actual != type) {
    if (PL_is_variable(t)) return PL_instantiation_error(t);
    return PL_type_error(type->name, t);
  }
  struct ObjStruct *o = data;
  if (o->h != h) {
    return PL_permission_error("access", type->name, t);
  }
  *ptr = o->ptr;
  return TRUE;
}

// ***************************** END BLOBS ********************************************


// TODO: Z3_solver_get_statistics

// TODO: make this handle_stats(h, A, B, C), print in PL.

static foreign_t handle_stats_foreign_locked(handle h, term_t handle_term, term_t num_declarations, term_t num_enum_sorts, term_t num_enum_declarations);

foreign_t handle_stats_foreign(term_t handle_term, term_t num_declarations, term_t num_enum_sorts, term_t num_enum_declarations) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = handle_stats_foreign_locked(h, handle_term, num_declarations, num_enum_sorts, num_enum_declarations);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t handle_stats_foreign_locked(handle h, term_t handle_term, term_t num_declarations, term_t num_enum_sorts, term_t num_enum_declarations) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

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


/*
  Error convention: argument errors (unbound or wrongly typed arguments, bad handles or models,
  out-of-range numbers) raise ISO error terms. A formula that is a valid Prolog term but not a valid
  Z3 formula (sort mismatch, undeclared function, wrong arity) fails, printing a message.
  An unbound variable anywhere in a formula is an argument error: see require_ground().
*/

// Raises instantiation_error unless t is ground.
static int require_ground(term_t t) {
  if (PL_is_ground(t)) return TRUE;
  return PL_instantiation_error(t);
}

foreign_t z3_new_handle_foreign(term_t handle_term) {
  if (!PL_is_variable(handle_term)) {
    return PL_uninstantiation_error(handle_term);
  }
  handle h = calloc(1, sizeof(struct HandleStruct));
  if (h == NULL) {
    return PL_resource_error("memory");
  }
  h->handle_id = atomic_fetch_add(&handle_counter, 1) + 1;
  atomic_init(&h->refcount, 1); // owned by the blob
  pthread_mutex_init(&h->lock, NULL);
  pthread_mutex_init(&h->pending_lock, NULL);
  initialize_handle(h);

  // The blob owns h from here; if the unification fails, garbage collection releases it.
  DEBUG("Made new handle %p\n", h);
  return PL_unify_blob(handle_term, h, sizeof(*h), &z3_handle_blob);
}

/*
  Deletes the handle's Z3 context now, rather than waiting for garbage collection.
  Afterwards the handle and its models raise existence errors.
*/
static foreign_t z3_free_handle_foreign_locked(handle h, term_t handle_term);

foreign_t z3_free_handle_foreign(term_t handle_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_free_handle_foreign_locked(h, handle_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_free_handle_foreign_locked(handle h, term_t handle_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  DEBUG("Freeing handle %p\n", h);
  destroy_context(h);
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
static foreign_t z3_reset_declarations_foreign_locked(handle h, term_t handle_term);

foreign_t z3_reset_declarations_foreign(term_t handle_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_reset_declarations_foreign_locked(h, handle_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_reset_declarations_foreign_locked(handle h, term_t handle_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_ast_map_reset(h->ctx, h->declarations);
  return TRUE;
}

/* Frees everything except for the handle itself. */

void free_handle_contents(handle h) {
  Z3_context ctx = h->ctx;
  DEBUG("freeing handle contents for %p\n", ctx);

  unsigned scopes = Z3_solver_get_num_scopes(ctx, h->solver);
  DEBUG("Scopes when freeing is %u\n", scopes);
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


// ************************* END GLOBALS *************************


// We need function declarations to make terms.

Z3_func_decl get_function_declaration(Z3_context ctx, decl_map declaration_map, const char *name_string, const size_t arity) {
  assert(declaration_map != NULL);

  DEBUG("current map size is %d\n", Z3_ast_map_size(ctx, declaration_map));
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
static foreign_t z3_declarations_string_foreign_locked(handle h, term_t handle_term, term_t result);

foreign_t z3_declarations_string_foreign(term_t handle_term, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_declarations_string_foreign_locked(h, handle_term, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_declarations_string_foreign_locked(handle h, term_t handle_term, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  decl_map declaration_map = h->declarations;
  Z3_context ctx = h->ctx;
  Z3_string rstring =  Z3_ast_map_to_string(ctx, declaration_map);
  return PL_unify_string_chars(result, rstring);
}

static foreign_t z3_enums_string_foreign_locked(handle h, term_t handle_term, term_t result);

foreign_t z3_enums_string_foreign(term_t handle_term, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_enums_string_foreign_locked(h, handle_term, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_enums_string_foreign_locked(handle h, term_t handle_term, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
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
  int rval = get_handle(handle_term, &h); // TODO: use ||
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

/**
foreign_t z3_free_solver_foreign(term_t handle_term, term_t u) {
  handle h;
  int rval = get_handle(handle_term, &h);
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

static foreign_t z3_free_model_foreign_locked(handle h, term_t handle_term, term_t model_term);

foreign_t z3_free_model_foreign(term_t handle_term, term_t model_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_free_model_foreign_locked(h, handle_term, model_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_free_model_foreign_locked(handle h, term_t handle_term, term_t model_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  model_ref m;
  rval = get_model_ref(model_term, h, &m);
  if (!rval) return rval;

  DEBUG("freeing model %p\n", (void *) m->model);
  Z3_model_dec_ref(h->ctx, m->model);
  m->model = NULL;
  m->h = NULL;
  handle_release_ref(h); // the handle blob still holds its own reference
  return TRUE;
}

/*
  Gets a model object from the solver; "Z3_solver_check" must have been run on the solver first.
  Otherwise, an error is reported and we fail.
  Unsafe, used for model_eval in Prolog; preferably use z3_model/1.
  Model should be freed after use, with z3_free_model/2.
*/

static foreign_t z3_get_model_foreign_locked(handle h, term_t handle_term, term_t model_term);

foreign_t z3_get_model_foreign(term_t handle_term, term_t model_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_get_model_foreign_locked(h, handle_term, model_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_get_model_foreign_locked(handle h, term_t handle_term, term_t model_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  Z3_solver solver = h->solver;

  Z3_model model = Z3_solver_get_model(h->ctx, solver);
  if (model == NULL) {
    return FALSE;
  }

  model_ref m = malloc(sizeof(struct ModelStruct));
  if (m == NULL) {
    return PL_resource_error("memory");
  }
  Z3_model_inc_ref(h->ctx, model);
  m->model = model;
  m->h = h;
  atomic_fetch_add(&h->refcount, 1);

  // The blob owns m from here; if the unification fails, garbage collection releases it.
  return PL_unify_blob(model_term, m, sizeof(*m), &z3_model_blob);
}



static foreign_t z3_model_eval_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t term_to_eval, term_t completion_flag, term_t result_term);

foreign_t z3_model_eval_foreign(term_t handle_term, term_t model_term, term_t term_to_eval, term_t completion_flag, term_t result_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_model_eval_foreign_locked(h, handle_term, model_term, term_to_eval, completion_flag, result_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_model_eval_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t term_to_eval, term_t completion_flag, term_t result_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  Z3_model model;
  rval = get_model(model_term, h, &model);
  if (!rval) return rval;

  int completion = FALSE;
  rval = PL_get_bool_ex(completion_flag, &completion);
  if (!rval) return rval;

  if (!require_ground(term_to_eval)) return FALSE;
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
    int ival; // Z3_mk_int_symbol takes an int, so fail on anything larger.
    int res = PL_get_integer(pl_term, &ival);
    if (!res) {
      ERROR("integer symbol out of range\n");
      return NULL;
    }
    Z3_symbol s = Z3_mk_int_symbol(ctx, ival);
    return s;
    break;
  }
  default: {
    char *fchars = NULL;
    int res = PL_get_chars(pl_term, &fchars, CVT_WRITE);
    ERROR("error making symbol %s, term type is %d\n", res ? fchars : NULL, term_type);
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
    if (!res) return FALSE;
    functor_t f = PL_new_functor(PL_new_atom(Z3_get_symbol_string(ctx, sname)), 1);
    if (!PL_cons_functor(cons_term, f, size_term)) {
      return FALSE;
    }
    break;
  default:
    {
      Z3_string sname_string = Z3_get_symbol_string(ctx, sname);
      int res = PL_put_atom_chars(cons_term, sname_string);
      if (!res) return FALSE;
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
    if (!z3_ast_to_term_internal(ctx, key, key_term)) {
      ERROR("could not convert declaration key %s\n", Z3_ast_to_string(ctx, key));
      Z3_ast_vector_dec_ref(ctx, keys);
      return FALSE;
    }

    Z3_func_decl value = (Z3_func_decl) Z3_ast_map_find(ctx, declaration_map, key);
    term_t value_term = PL_new_term_ref();
    Z3_sort sort = Z3_get_range(ctx, value);

    bool res = z3_sort_to_term(ctx, sort, value_term);
    if (!res) {
      ERROR("error in z3_sort_to_term\n");
      Z3_ast_vector_dec_ref(ctx, keys);
      return FALSE;
    }

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

static foreign_t z3_get_enum_declarations_foreign_locked(handle h, term_t handle_term, term_t result);

foreign_t z3_get_enum_declarations_foreign(term_t handle_term, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_get_enum_declarations_foreign_locked(h, handle_term, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_get_enum_declarations_foreign_locked(handle h, term_t handle_term, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  return z3_declaration_map_to_term(h->ctx, h->enum_declarations, result);
}

static foreign_t z3_get_declarations_foreign_locked(handle h, term_t handle_term, term_t result);

foreign_t z3_get_declarations_foreign(term_t handle_term, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_get_declarations_foreign_locked(h, handle_term, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_get_declarations_foreign_locked(handle h, term_t handle_term, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  return z3_declaration_map_to_term(h->ctx, h->declarations, result);
}


// Declare enumerations:
// can only be called once for a given enum name, per context.
// The resulting Z3_sort can be used by mk_var(ctx, varname, sort) or mk_func_decl.
// enums are accumulated in h->enum_declarations.

// +atom, +list
static foreign_t z3_declare_enum_foreign_locked(handle h, term_t handle_term, term_t sort_name_term, term_t enum_names_list);

foreign_t z3_declare_enum_foreign(term_t handle_term, term_t sort_name_term, term_t enum_names_list) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_declare_enum_foreign_locked(h, handle_term, sort_name_term, enum_names_list);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_declare_enum_foreign_locked(handle h, term_t handle_term, term_t sort_name_term, term_t enum_names_list) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  Z3_context ctx = h->ctx;

  char * sort_name_string;
  if (!PL_get_atom_chars(sort_name_term, &sort_name_string)) {
    if (PL_is_variable(sort_name_term)) return PL_instantiation_error(sort_name_term);
    return PL_type_error("atom", sort_name_term);
  }
  size_t n;
  switch (PL_skip_list(enum_names_list, 0, &n)) { // also gets list length
  case PL_LIST:
    break;
  case PL_PARTIAL_LIST:
    return PL_instantiation_error(enum_names_list);
  default:
    return PL_type_error("list", enum_names_list);
  }
  if (!PL_is_ground(enum_names_list)) {
    return PL_instantiation_error(enum_names_list);
  }
  if (n == 0) {
    return PL_domain_error("non_empty_list", enum_names_list);
  }

  const Z3_symbol sort_name = mk_symbol(ctx, sort_name_term);
  if (sort_name == NULL) {
    return FALSE;
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
  DEBUG("Names has length %lu\n", n);
  Z3_symbol *enum_names = malloc(sizeof(Z3_symbol) * n);

  // here we go through the names list and put them in enum_names; see https://www.swi-prolog.org/pldoc/man?section=foreign-read-list
  term_t head = PL_new_term_ref();   // the elements
  term_t tail = PL_copy_term_ref(enum_names_list); // copy (we modify tail)
  size_t i = 0;
  while( PL_get_list_ex(tail, head, tail) )
    {
      Z3_symbol a = mk_symbol(ctx, head);
      if (a == NULL) {
        free(enum_names);
        return PL_type_error("atom", head);
      }
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
  if (!Z3_ast_map_contains(ctx, map, key)) {
    ERROR("Key %s not found\n", keyname);
    return FALSE;
  }
  // INFO("Key %s found\n", keyname);
  Z3_ast_map_erase(ctx, map, key);
  return TRUE;
}


static foreign_t z3_remove_declaration_foreign_locked(handle h, term_t handle_term, term_t name_term, term_t arity_term);

foreign_t z3_remove_declaration_foreign(term_t handle_term, term_t name_term, term_t arity_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_remove_declaration_foreign_locked(h, handle_term, name_term, arity_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_remove_declaration_foreign_locked(handle h, term_t handle_term, term_t name_term, term_t arity_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  int arity;
  char *name_string;
  if (!PL_get_atom_chars(name_term, &name_string)) {
    if (PL_is_variable(name_term)) return PL_instantiation_error(name_term);
    return PL_type_error("atom", name_term);
  }
  rval = PL_get_integer_ex(arity_term, &arity);
  if (!rval) return rval;
  if (arity < 0) {
    return PL_domain_error("not_less_than_zero", arity_term);
  }
  DEBUG("removing declaration for %s\n", name_string);
  return remove_declaration(h->ctx, h->declarations, name_string, arity);
}

/*
  For debugging:
*/

static foreign_t z3_symbol_foreign_locked(handle h, term_t handle_term, term_t i, term_t symbol);

foreign_t z3_symbol_foreign(term_t handle_term, term_t i, term_t symbol) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_symbol_foreign_locked(h, handle_term, i, symbol);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_symbol_foreign_locked(handle h, term_t handle_term, term_t i, term_t symbol) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  DEBUG("term types: %d %d\n", PL_term_type(i), PL_term_type(symbol));

  Z3_symbol s = mk_symbol(h->ctx, i);
  if (s == NULL) {
    // return PL_warning("z3_symbol/2: should specify an int, atom, or string");
    return FALSE;
  }
  return unify_obj(symbol, &z3_symbol_blob, h, s);
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
  ERROR("unexpected Z3_lbool value %d\n", (int) status);
  return FALSE;
}

/* For debugging: converts a z3_ast blob (from term_to_z3_ast/3) back to a Prolog term. */

static foreign_t z3_ast_to_term_foreign_locked(handle h, term_t handle_term, term_t ast_term, term_t term);

foreign_t z3_ast_to_term_foreign(term_t handle_term, term_t ast_term, term_t term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_ast_to_term_foreign_locked(h, handle_term, ast_term, term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_ast_to_term_foreign_locked(handle h, term_t handle_term, term_t ast_term, term_t term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_ast ast;
  rval = get_obj(ast_term, &z3_ast_blob, h, (void **) &ast);
  if (!rval) {
    return rval;
  }
  return z3_ast_to_term_internal(h->ctx, ast, term);
}


// get a Prolog list with the assertions added to a solver:
// +Solver, -List
static foreign_t z3_solver_assertions_foreign_locked(handle h, term_t handle_term, term_t list);

foreign_t z3_solver_assertions_foreign(term_t handle_term, term_t list) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_solver_assertions_foreign_locked(h, handle_term, list);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_solver_assertions_foreign_locked(handle h, term_t handle_term, term_t list) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_solver solver = h->solver;
  Z3_context ctx = h->ctx;
  Z3_ast_vector v = Z3_solver_get_assertions(ctx, solver);
  Z3_ast_vector_inc_ref(ctx, v);
  unsigned size = Z3_ast_vector_size(ctx, v);
  DEBUG("Vector size is %u\n", size);
  term_t l = PL_new_term_ref();
  PL_put_nil(l);
  for (unsigned i = 0; i < size; ++i) {
    term_t a = PL_new_term_ref(); // putting this outside the loop does not work.
    Z3_ast termi = Z3_ast_vector_get(ctx, v, i);
    if (!z3_ast_to_term_internal(ctx, termi, a)) {
      ERROR("could not convert assertion %s\n", Z3_ast_to_string(ctx, termi));
      Z3_ast_vector_dec_ref(ctx, v);
      return FALSE;
    }
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
    if (Z3_get_numeral_small(ctx, ast, &num, &den)) {
      ERROR("numeral_small succeeded were numeral_rational_int64 did not\n");
      return FALSE;
    }
    Z3_string str = Z3_get_numeral_string(ctx, ast);
    DEBUG("Handling numeral term %s\n", str);
    term_t t = PL_new_term_ref();
    if (!PL_chars_to_term(str, t)) {
      ERROR("PL_chars_to_term failed for %s\n", str);
      return FALSE;
    }
    return PL_unify(term, t);
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


static foreign_t term_to_z3_ast_foreign_locked(handle h, term_t handle_term, term_t formula, term_t result);

foreign_t term_to_z3_ast_foreign(term_t handle_term, term_t formula, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = term_to_z3_ast_foreign_locked(h, handle_term, formula, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t term_to_z3_ast_foreign_locked(handle h, term_t handle_term, term_t formula, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  
  if (!require_ground(formula)) return FALSE;
  Z3_ast z3_ast = term_to_ast(h, h->declarations, formula);
  if (z3_ast == NULL) {
    return FALSE;
  }
  return unify_obj(result, &z3_ast_blob, h, z3_ast);
}


/*
  For debugging: convert Z3 ast to a Prolog string:
*/

static foreign_t z3_ast_string_foreign_locked(handle h, term_t handle_term, term_t formula, term_t result);

foreign_t z3_ast_string_foreign(term_t handle_term, term_t formula, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_ast_string_foreign_locked(h, handle_term, formula, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_ast_string_foreign_locked(handle h, term_t handle_term, term_t formula, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_ast z3_form;
  rval = get_obj(formula, &z3_ast_blob, h, (void **) &z3_form);
  if (!rval) {
    return rval;
  }
  Z3_string rstring = Z3_ast_to_string(h->ctx, z3_form);
  return PL_unify_string_chars(result, rstring);
}

/*
  Does one push on the solver; output is the new number of scopes for the solver.
*/

static foreign_t z3_solver_push_foreign_locked(handle h, term_t handle_term, term_t output_term);

foreign_t z3_solver_push_foreign(term_t handle_term, term_t output_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_solver_push_foreign_locked(h, handle_term, output_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_solver_push_foreign_locked(handle h, term_t handle_term, term_t output_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  const Z3_solver solver = h->solver;
  const Z3_context ctx = h->ctx;
  // Unify before pushing, so that a mismatched output fails without leaving an extra scope.
  const unsigned new_scopes = Z3_solver_get_num_scopes(ctx, solver) + 1;
  if (!PL_unify_uint64(output_term, new_scopes)) {
    return FALSE;
  }
  Z3_solver_push(ctx, solver);
  assert(Z3_solver_get_num_scopes(ctx, solver) == new_scopes);
  return TRUE;
}

/* Pops the solver npops times. Output is the new number of scopes for the solver. */

static foreign_t z3_solver_pop_foreign_locked(handle h, const term_t npops, term_t output_term);

foreign_t z3_solver_pop_foreign(const term_t handle_term, const term_t npops, term_t output_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_solver_pop_foreign_locked(h, npops, output_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_solver_pop_foreign_locked(handle h, const term_t npops, term_t output_term) {
  int rval;
  Z3_solver solver = h->solver;

  int nbacktrack;
  rval = PL_get_integer_ex(npops, &nbacktrack);
  if (!rval) return rval;
  if (nbacktrack < 0) {
    return PL_domain_error("not_less_than_zero", npops);
  }

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
*/

static foreign_t z3_assert_foreign_locked(handle h, term_t handle_term, term_t formula);

foreign_t z3_assert_foreign(term_t handle_term, term_t formula) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_assert_foreign_locked(h, handle_term, formula);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_assert_foreign_locked(handle h, term_t handle_term, term_t formula) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  DEBUG("got handle\n");
  if (!require_ground(formula)) return FALSE;
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


static foreign_t z3_solver_scopes_foreign_locked(handle h, term_t handle_term, term_t result);

foreign_t z3_solver_scopes_foreign(term_t handle_term, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_solver_scopes_foreign_locked(h, handle_term, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_solver_scopes_foreign_locked(handle h, term_t handle_term, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  unsigned scopes = Z3_solver_get_num_scopes(h->ctx, h->solver);
  return PL_unify_uint64(result, scopes);
}

static foreign_t z3_check_foreign_locked(handle h, term_t handle_term, term_t status_arg);

foreign_t z3_check_foreign(term_t handle_term, term_t status_arg) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_check_foreign_locked(h, handle_term, status_arg);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_check_foreign_locked(handle h, term_t handle_term, term_t status_arg) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_solver solver = h->solver;
  const Z3_context ctx = h->ctx;
  DEBUG("Checking solver %p with context %p\n", solver, ctx);

  Z3_lbool check_status = Z3_solver_check(ctx, solver);
  DEBUG("did check, status %d\n", check_status);
  rval = z3_lbool_to_atom(check_status, status_arg);
  DEBUG("did status to atom %d\n", rval);
  return rval;
}


static foreign_t z3_check_and_print_foreign_locked(handle h, term_t handle_term, term_t status_arg);

foreign_t z3_check_and_print_foreign(term_t handle_term, term_t status_arg) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_check_and_print_foreign_locked(h, handle_term, status_arg);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_check_and_print_foreign_locked(handle h, term_t handle_term, term_t status_arg) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
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



// Makes a function (or constant) declaration.
// Example: z3_declare_function(f(int, bool), int, R).
// Example: z3_declare_function(f(int, int), int, X)

// Note: This does not handle the case where formula is not ground.

static foreign_t z3_declare_function_foreign_locked(handle h, term_t handle_term, const term_t formula, const term_t range, term_t result);

foreign_t z3_declare_function_foreign(term_t handle_term, const term_t formula, const term_t range, term_t result) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_declare_function_foreign_locked(h, handle_term, formula, range, result);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_declare_function_foreign_locked(handle h, term_t handle_term, const term_t formula, const term_t range, term_t result) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  atom_t name;

  size_t arity;
  // Variables should not be declared directly; z3.pl uses attributes for them.
  if (!require_ground(formula) || !require_ground(range)) return FALSE;
  if (!PL_get_name_arity(formula, &name, &arity)) {
    return PL_type_error("callable", formula);
  }
  if (!PL_is_callable(range)) {
    return PL_type_error("callable", range);
  }

  Z3_func_decl decl = make_function_declaration(h, formula, range);
  if (decl == NULL) {
    DEBUG("failing, mk_func_decl is NULL\n");
    return FALSE;
  }
  return unify_obj(result, &z3_ast_blob, h, Z3_func_decl_to_ast(h->ctx, decl));
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


static foreign_t z3_model_functions_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t list);

foreign_t z3_model_functions_foreign(term_t handle_term, term_t model_term, term_t list) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_model_functions_foreign_locked(h, handle_term, model_term, list);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_model_functions_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t list) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  const Z3_context ctx = h->ctx;
  Z3_model model;
  rval = get_model(model_term, h, &model);
  if (!rval) return rval;

  Z3_model_inc_ref(ctx, model);
  rval = model_functions(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}

static foreign_t z3_model_constants_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t list);

foreign_t z3_model_constants_foreign(term_t handle_term, term_t model_term, term_t list) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_model_constants_foreign_locked(h, handle_term, model_term, list);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_model_constants_foreign_locked(handle h, term_t handle_term, term_t model_term, term_t list) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
  Z3_context ctx = h->ctx;
  Z3_model model;
  rval = get_model(model_term, h, &model);
  if (!rval) return rval;
  Z3_model_inc_ref(ctx, model);
  rval = model_constants(ctx, model, list);
  Z3_model_dec_ref(ctx, model);
  return rval;
}

// useful to check validity of handle-related things. (The pointer itself is not enough, could be reused.)
static foreign_t z3_handle_id_foreign_locked(handle h, term_t handle_term, term_t result_term);

foreign_t z3_handle_id_foreign(term_t handle_term, term_t result_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_handle_id_foreign_locked(h, handle_term, result_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_handle_id_foreign_locked(handle h, term_t handle_term, term_t result_term) {
  int rval = TRUE;
  (void) rval; (void) handle_term;
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
      if (width <= 0) {
        ERROR("bit-vector width should be positive, got %d\n", width);
        return NULL;
      }
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
    // Entry points check groundness first (require_ground), so this is a backstop.
    PL_instantiation_error(expression);
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
  Builds the Z3 AST for a compound term whose arguments have already been converted to "subterms".
  Returns NULL on failure. Does not free subterms; the caller owns them, so early returns here are safe.
*/

static Z3_ast compound_to_ast(const handle h, decl_map declaration_map, const char *name_string,
                              const size_t arity, Z3_ast *subterms) {
  const Z3_context ctx = h->ctx;
  Z3_ast result = NULL;

  // ********************************************* built-in compound term_to_ast  ****************************************/
  
  if (strcmp(name_string, "mk_rational")==0) {
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_simplify(ctx, Z3_mk_div(ctx,
                                        Z3_mk_int2real(ctx, subterms[0]),
                                        Z3_mk_int2real(ctx, subterms[1]))
                         );
  }
  else if (strcmp(name_string, "+") == 0 ) {
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
    if (s1 != s2 && !(arith_sort(ctx, s1) && arith_sort(ctx, s2))) // Z3 allows mixing Int and Real only
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
  // between, inclusive of both endpoints (as in python):
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
      special cases, because they have an extra arg:
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
    result = Z3_mk_bvnand(ctx, subterms[0], subterms[1]);
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
  return result;
}


static predicate_t rational_pred = NULL;

/* terms must be a term_t vector of size 3 */
bool split_rational(term_t terms) {
  if (!rational_pred) {
    rational_pred = PL_predicate("rational", 3, NULL);
  }
  qid_t qid = PL_open_query(NULL, PL_Q_NORMAL, rational_pred, terms);
  int r = PL_next_solution(qid);
  if (!r) {
    ERROR("PL_next_solution failed");
    PL_close_query(qid);
    return false;
  }
  r = PL_cut_query(qid);
  if (!r) {
    ERROR("PL_cut_query failed.");
  }
  return true;
}

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
    // Entry points check groundness first (require_ground), so this is a backstop.
    PL_instantiation_error(formula);
    return NULL;

  // ********************************************* atom, string, integer cases ****************************************/
  case PL_ATOM: {
    char *atom_string;
    int res = PL_get_atom_chars(formula, &atom_string);
    if (!res) {
      return NULL;
    }
    // Only the atoms true and false are Boolean constants. (PL_get_bool would also accept on, off, and fail.)
    if (strcmp(atom_string, "true") == 0) {
      return Z3_mk_true(ctx);
    }
    if (strcmp(atom_string, "false") == 0) {
      return Z3_mk_false(ctx);
    }
    DEBUG("term_to_ast, atom %s\n", atom_string);

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
      DEBUG("Found function %s declaration %s\n", atom_string, Z3_func_decl_to_string(ctx, declaration));
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
    if (PL_get_long(formula, &lval)) {
      DEBUG("Got PL_get_long\n");
      Z3_sort INT_SORT = Z3_mk_int_sort(ctx);
      return Z3_mk_int64(ctx, lval, INT_SORT);
    }
    else {
      char *int_string;
      if (PL_get_chars(formula, &int_string, CVT_INTEGER)) {
        result = Z3_mk_numeral(ctx, int_string, h->int_sort);
        if (result == NULL) {
          ERROR("Z3_mk_numeral failed for %s\n", int_string);
        }
        return result;
      }
      else {
        ERROR("PL_get_chars failed for integer\n");
        return NULL;
      }
    }
    /**** This would be useful if we could convert mpz to Z3 directly.
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
    ************/
    break;
  case PL_RATIONAL: {
    term_t trefs = PL_new_term_refs(3);
    if (!PL_unify(trefs, formula)) {
      ERROR("PL_unify failed for PL_RATIONAL\n");
      return NULL;
    }
    term_t num = trefs + 1;
    term_t den = trefs + 2;
    if (split_rational(trefs)) {
      DEBUG("split_rational worked!\n");
      Z3_ast num_ast = term_to_ast(h, declaration_map, num);
      Z3_ast den_ast = term_to_ast(h, declaration_map, den);
      if (num_ast == NULL || den_ast == NULL) {
        ERROR("could not convert numerator or denominator of rational\n");
        return NULL;
      }
      result = Z3_mk_div(ctx, Z3_mk_int2real(ctx, num_ast), Z3_mk_int2real(ctx, den_ast));
      return result;
    }
    else {
      ERROR("split_rational failed\n");
      // Could look at PL_get_mpq; but better to handle this in Prolog with rational/3.
      return NULL;
    }
  }
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
      ERROR("PL_get_chars failed for float\n");
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
      if (PL_skip_list(list_term, 0, &width) != PL_LIST || width == 0) { // also gets list length
        ERROR("Argument to bv_numeral should be a non-empty proper list of booleans\n");
        return NULL;
      }
      bool * bits = malloc(width * sizeof(bool));
      term_t head = PL_new_term_ref();   // the elements
      term_t tail = PL_copy_term_ref(list_term); // copy (we modify tail)
      size_t i = 0;
      while (PL_get_list(tail, head, tail)) {
        int b;
        if (!PL_get_bool(head, &b)) {
          char *elem_string = NULL;
          if (!PL_get_chars(head, &elem_string, CVT_WRITE)) elem_string = "?";
          ERROR("bv_numeral: %s is not a boolean\n", elem_string);
          free(bits);
          return NULL;
        }
        assert(i < width);
        bits[i] = b;
        i++;
      }

      result = Z3_mk_bv_numeral(ctx, width, bits);
      free(bits);
      return result;
    }

    // TODO: special cases for mk_numeral and mk_unsigned_int64. Both use an int and a sort as an argument.
    // we don't do unsigned_int because PL does not have it, could be confusing.

    if (strcmp(name_string, MK_NUMERAL)==0 ||
        strcmp(name_string, "mk_unsigned_int64")==0) { // confusing name, makes something of the specified sort.
      CHECK_ARITY(name_string, 2, arity);
      // get sort from second argument:
      DEBUG("numeral/unsigned_int64 case\n");
      term_t sort_term = PL_new_term_ref();
      res = PL_get_arg(2, formula, sort_term);
      if (!res) return NULL;
      Z3_sort sort = mk_sort(h, sort_term);
      if (sort == NULL) {
        ERROR("%s: could not make sort\n", name_string);
        return NULL;
      }
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
      else { // unsigned_int64 case:
        uint64_t uint;
        if (!PL_get_uint64(arg_term, &uint)) {
          ERROR("First argument to mk_unsigned_int64 should be a non-negative 64-bit integer\n");
          return NULL;
        }
        return Z3_mk_unsigned_int64(ctx, uint, sort);
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
      if (arg == NULL) return NULL;
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
      if (!PL_get_integer(sub1, &width) || width <= 0) {
        ERROR("First argument to int2bv should be a positive integer\n");
        return NULL;
      }
      Z3_ast arg = term_to_ast(h, declaration_map, sub2);
      if (arg == NULL) return NULL;
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
      if (arg1 == NULL) return NULL;
      Z3_ast arg2 = term_to_ast(h, declaration_map, sub2);
      if (arg2 == NULL) return NULL;

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
      

    result = compound_to_ast(h, declaration_map, name_string, arity, subterms);
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

// +handle, +Term, -Term.
static foreign_t z3_simplify_foreign_locked(handle h, term_t handle_term, term_t tin, term_t tout);

foreign_t z3_simplify_foreign(term_t handle_term, term_t tin, term_t tout) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_simplify_foreign_locked(h, handle_term, tin, tout);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_simplify_foreign_locked(handle h, term_t handle_term, term_t tin, term_t tout) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

  Z3_context ctx = h->ctx;
  decl_map declaration_map = h->declarations;

  if (!require_ground(tin)) return FALSE;
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
static foreign_t map_test_foreign_locked(handle h, term_t handle_term, term_t string_atom);

foreign_t map_test_foreign(term_t handle_term, term_t string_atom) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = map_test_foreign_locked(h, handle_term, string_atom);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t map_test_foreign_locked(handle h, term_t handle_term, term_t string_atom) {
  int rval = TRUE;
  (void) rval; (void) handle_term;

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

install_t install_z3_swi_foreign(void)
{
  DEBUG("Installing Z3 package\n");

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
  PRED("term_to_z3_ast", 3, term_to_z3_ast_foreign, 0); // +handle, +formula, -z3_ast
  PRED("z3_ast_string", 3, z3_ast_string_foreign, 0); // +handle, +formula, -string
  PRED("z3_ast_to_term", 3, z3_ast_to_term_foreign, 0); // +handle, +ast, -formula
  PRED("z3_symbol", 3, z3_symbol_foreign, 0); // +handle, +formula, -z3_symbol

  PRED("z3_declare_function", 4, z3_declare_function_foreign, 0); // +handle_term, +pl_term, +range_atom, -z3_ast (the declaration)
  PRED("z3_declare_enum", 3, z3_declare_enum_foreign, 0);

  PRED("z3_solver_push", 2, z3_solver_push_foreign, 0); // +handle, -num_scopes
  PRED("z3_solver_pop", 3, z3_solver_pop_foreign, 0); // +handle, +numpops, -num_scopes

  PRED("z3_solver_scopes", 2, z3_solver_scopes_foreign, 0); // +handle, -num_scopes):
  PRED("z3_check", 2, z3_check_foreign, 0); // +handle, -status
  PRED("z3_check_and_print", 2, z3_check_and_print_foreign, 0); // +handle, -status

  PRED("z3_get_model", 2, z3_get_model_foreign, 0); // +handle, -model
  PRED("z3_model_eval", 5, z3_model_eval_foreign, 0); // +handle, +model, +formula, +completion_flag, -value
  PRED("z3_free_model", 2, z3_free_model_foreign, 0); // +handle, +model

  PRED("z3_simplify", 3, z3_simplify_foreign, 0); // +handle, +term, -simplified_term
  PRED("z3_solver_assertions", 2, z3_solver_assertions_foreign, 0); // +handle, -assertion_list

  PRED("z3_model_functions", 3, z3_model_functions_foreign, 0); // +handle, +model, -functions_term
  PRED("z3_model_constants", 3, z3_model_constants_foreign, 0); // +handle, +model, -constants_term

  PRED("z3_reset_declarations", 1, z3_reset_declarations_foreign, 0); // +handle // clears non-enum declarations, keeps enums and the Z3 context
  PRED("z3_get_enum_declarations", 2, z3_get_enum_declarations_foreign, 0); // +handle, -term
  PRED("z3_get_declarations", 2, z3_get_declarations_foreign, 0); // +handle, -term

  // for debugging:
  PRED("z3_declarations_string", 2, z3_declarations_string_foreign, 0); // +handle, -string
  PRED("z3_enums_string", 2, z3_enums_string_foreign, 0); // +handle, -string

  PRED("z3_remove_declaration", 3, z3_remove_declaration_foreign, 0); // +handle, +name, +arity

  PRED("z3_handle_id", 2, z3_handle_id_foreign, 0); // -context id
  PRED("map_test", 1, map_test_foreign, 0); //

  PRED("z3_new_handle", 1, z3_new_handle_foreign, 0); // -handle
  PRED("z3_free_handle", 1, z3_free_handle_foreign, 0); // +handle

  PRED("z3_alloc_bytes", 1, z3_alloc_bytes_foreign, 0); // +size
  PRED("z3_finalize_memory", 0, z3_finalize_memory_foreign, 0); // +size // debugging only, dangerous.

  PRED("handle_stats", 4, handle_stats_foreign, 0); // +handle, -A, -B, -C
  
}
