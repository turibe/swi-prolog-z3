
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <stdatomic.h>
#include <pthread.h>
#include <time.h>
#include <limits.h>
#include <math.h>

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

// Prints the result of a check of solver s, and its model if there is one.
void print_check_result(Z3_context ctx, Z3_solver s, Z3_lbool result)
{
    Z3_model m      = 0;
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
}


typedef Z3_ast_map decl_map;
typedef Z3_ast_map sort_map;

// ***************************** GLOBAL VARIABLES ********************************************


static atomic_long handle_counter = 0;

// Z3 contexts that exist right now, counted so z3_finalize_memory/0 can refuse to run while any do:
// Z3_finalize_memory frees memory that every context relies on. contexts_lock makes creating a
// context and finalizing mutually exclusive. The count goes down only after Z3_del_context returns.
static atomic_long live_contexts = 0;
static pthread_mutex_t contexts_lock = PTHREAD_MUTEX_INITIALIZER;

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
  Z3_sort int_sort, bool_sort, real_sort, string_sort;
  unsigned timeout_ms;          // from z3_set_timeout/2, 0 for none; also given to optimizers
  struct bound_variable *bound; // quantifier variables in scope while term_to_ast converts a body
  size_t num_bound, max_bound;

  pthread_mutex_t lock;          // held for the whole of any predicate that uses this handle
  atomic_int refcount;           // handle blob + one per live model blob
  pthread_mutex_t pending_lock;  // protects ctx becoming NULL and the pending_models list
  Z3_model *pending_models;      // models garbage collected but not yet released in Z3
  size_t num_pending, max_pending;
};

typedef struct HandleStruct *handle;

struct bound_variable {
  atom_t name;
  Z3_ast constant;  // the constant that Z3_mk_forall_const/exists_const binds
};

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
  handle->string_sort = Z3_mk_string_sort(ctx);

}

// ***************************** HANDLE AND MODEL BLOBS ********************************************

// Drops one reference to h, freeing the struct when it was the last one. The context must already be deleted.
static void handle_release_ref(handle h) {
  if (atomic_fetch_sub(&h->refcount, 1) == 1) {
    assert(h->ctx == NULL);
    pthread_mutex_destroy(&h->lock);
    pthread_mutex_destroy(&h->pending_lock);
    free(h->pending_models);
    free(h->bound);
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
    atomic_fetch_sub(&live_contexts, 1);
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

/*
  Runs Z3_solver_check on h's solver so that Prolog signals still reach this thread: a time limit
  (call_with_time_limit/2), thread_signal/2 or Ctrl-C. Z3 does not return to its caller while it
  searches, so the check runs on a helper thread while this one waits, handling signals every
  CHECK_POLL_MS. If a handler raises an exception, Z3_interrupt stops the check, and this returns
  FALSE, with the exception pending, once the helper has finished. Otherwise it sets *result.
  The caller holds h->lock, so nothing else uses the context meanwhile; the helper makes no
  Prolog calls.
*/
#define CHECK_POLL_MS 10
#define CHECK_STACK_SIZE (256 * 1024 * 1024) // Z3 can recurse deeply; this is only reserved, not used

struct check_job {
  Z3_context ctx;
  Z3_solver solver;
  Z3_optimize optimize;      // if not NULL, check this instead of the solver
  unsigned num_assumptions;  // 0 for a plain check
  Z3_ast *assumptions;
  Z3_lbool result;
  int done;
  pthread_mutex_t mutex;
  pthread_cond_t finished;
};

static void *run_check(void *arg) {
  struct check_job *job = arg;
  Z3_lbool result = job->optimize != NULL
    ? Z3_optimize_check(job->ctx, job->optimize, 0, NULL)
    : job->num_assumptions == 0
    ? Z3_solver_check(job->ctx, job->solver)
    : Z3_solver_check_assumptions(job->ctx, job->solver, job->num_assumptions, job->assumptions);
  pthread_mutex_lock(&job->mutex);
  job->result = result;
  job->done = TRUE;
  pthread_cond_signal(&job->finished);
  pthread_mutex_unlock(&job->mutex);
  return NULL;
}

// Runs the check described by job (see interruptible_check) on a helper thread, handling signals.
static int interruptible_run(handle h, struct check_job *job_in, Z3_lbool *result) {
  struct check_job job = *job_in;
  job.result = Z3_L_UNDEF;
  job.done = FALSE;
  pthread_mutex_init(&job.mutex, NULL);
  pthread_cond_init(&job.finished, NULL);
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, CHECK_STACK_SIZE);
  pthread_t helper;
  int started = pthread_create(&helper, &attr, run_check, &job) == 0;
  pthread_attr_destroy(&attr);
  int raised = FALSE;
  if (!started) {
    run_check(&job); // no thread: check here, uninterruptibly
  }
  else {
    pthread_mutex_lock(&job.mutex);
    while (!job.done) {
      struct timespec deadline;
      clock_gettime(CLOCK_REALTIME, &deadline);
      deadline.tv_nsec += CHECK_POLL_MS * 1000000L;
      if (deadline.tv_nsec >= 1000000000L) { deadline.tv_sec += 1; deadline.tv_nsec -= 1000000000L; }
      pthread_cond_timedwait(&job.finished, &job.mutex, &deadline);
      if (!job.done && !raised) {
        pthread_mutex_unlock(&job.mutex);
        if (PL_handle_signals() < 0) { // a handler raised an exception: stop the search
          raised = TRUE;
          Z3_interrupt(h->ctx);
        }
        pthread_mutex_lock(&job.mutex);
      }
    }
    pthread_mutex_unlock(&job.mutex);
    pthread_join(helper, NULL);
  }
  pthread_cond_destroy(&job.finished);
  pthread_mutex_destroy(&job.mutex);
  *result = job.result;
  return !raised;
}

// As interruptible_check, under the given assumptions (Z3_solver_check_assumptions).
static int interruptible_check_assumptions(handle h, unsigned n, Z3_ast *assumptions, Z3_lbool *result) {
  struct check_job job = { .ctx = h->ctx, .solver = h->solver, .num_assumptions = n, .assumptions = assumptions };
  return interruptible_run(h, &job, result);
}

static int interruptible_check(handle h, Z3_lbool *result) {
  return interruptible_check_assumptions(h, 0, NULL, result);
}

// As interruptible_check, for an optimizer (Z3_optimize_check).
static int interruptible_optimize(handle h, Z3_optimize optimize, Z3_lbool *result) {
  struct check_job job = { .ctx = h->ctx, .optimize = optimize };
  return interruptible_run(h, &job, result);
}


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
  pthread_mutex_lock(&contexts_lock);
  initialize_handle(h);
  atomic_fetch_add(&live_contexts, 1);
  pthread_mutex_unlock(&contexts_lock);

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

/*
  Frees Z3's global memory (Z3_finalize_memory), for leak checking. Z3 needs that memory for every
  context, so this raises permission_error(finalize, z3_memory, live_handles(N)) instead while any
  handle's context exists. That includes handles that are no longer referenced but not yet garbage
  collected; call garbage_collect_atoms/0 first. Z3 can be used again afterwards.
*/
foreign_t z3_finalize_memory_foreign(void) {
  pthread_mutex_lock(&contexts_lock);
  long live = atomic_load(&live_contexts);
  if (live > 0) {
    pthread_mutex_unlock(&contexts_lock);
    term_t culprit = PL_new_term_ref();
    if (!PL_unify_term(culprit, PL_FUNCTOR_CHARS, "live_handles", 1, PL_LONG, live)) return FALSE;
    return PL_permission_error("finalize", "z3_memory", culprit);
  }
  Z3_finalize_memory();
  pthread_mutex_unlock(&contexts_lock);
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


/*
  A floating-point sort as a Prolog term: float16, float32, float64 or float128 for the IEEE
  formats, as accepted by mk_sort, and fp(Ebits, Sbits) otherwise; the rounding-mode sort is
  roundingmode.
*/
static int fp_sort_to_term(Z3_context ctx, Z3_sort sort, term_t term) {
  if (Z3_get_sort_kind(ctx, sort) == Z3_ROUNDING_MODE_SORT) return PL_put_atom_chars(term, "roundingmode");
  unsigned e = Z3_fpa_get_ebits(ctx, sort), s = Z3_fpa_get_sbits(ctx, sort);
  if (e == 5 && s == 11)   return PL_put_atom_chars(term, "float16");
  if (e == 8 && s == 24)   return PL_put_atom_chars(term, "float32");
  if (e == 11 && s == 53)  return PL_put_atom_chars(term, "float64");
  if (e == 15 && s == 113) return PL_put_atom_chars(term, "float128");
  term_t widths = PL_new_term_refs(2);
  return PL_put_int64(widths, e) && PL_put_int64(widths + 1, s)
    && PL_cons_functor(term, PL_new_functor(PL_new_atom("fp"), 2), widths, widths + 1);
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
  case Z3_FLOATING_POINT_SORT:
  case Z3_ROUNDING_MODE_SORT:
    if (!fp_sort_to_term(ctx, sort, cons_term)) return FALSE;
    break;
  case Z3_ARRAY_SORT: {
    term_t parts = PL_new_term_refs(2);
    if (!z3_sort_to_term(ctx, Z3_get_array_sort_domain(ctx, sort), parts)
        || !z3_sort_to_term(ctx, Z3_get_array_sort_range(ctx, sort), parts + 1)
        || !PL_cons_functor(cons_term, PL_new_functor(PL_new_atom("array"), 2), parts, parts + 1)) {
      return FALSE;
    }
    break;
  }
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

/*
  Converts an irrational algebraic number, which Z3 produces in models of nonlinear real arithmetic,
  to algebraic(Approx, root(Coefficients, Index)):
    - Approx is a Prolog float close to the value;
    - Coefficients lists the integer coefficients of its defining polynomial, lowest degree first,
      so [-2, 0, 1] is x^2 - 2;
    - Index says which real root of that polynomial it is, counting from 1 in increasing order.
  For example, the positive square root of 2 is algebraic(1.4142135623730951, root([-2, 0, 1], 2)).
*/
#define ALGEBRAIC_DECIMAL_PLACES 20 // more than a double holds, so the float is correctly rounded

static int algebraic_to_term(const Z3_context ctx, Z3_ast ast, term_t term) {
  // Z3 marks a decimal approximation with a trailing '?'; strip it before parsing.
  Z3_string decimal = Z3_get_numeral_decimal_string(ctx, ast, ALGEBRAIC_DECIMAL_PLACES);
  size_t len = strlen(decimal);
  char *digits = malloc(len + 1);
  if (digits == NULL) return PL_resource_error("memory");
  memcpy(digits, decimal, len + 1);
  if (len > 0 && digits[len - 1] == '?') digits[len - 1] = '\0';
  term_t parsed = PL_new_term_ref();
  double approx;
  int ok = PL_chars_to_term(digits, parsed) && PL_get_float(parsed, &approx);
  if (!ok) ERROR("could not parse algebraic number approximation %s\n", digits);
  free(digits);
  if (!ok) return FALSE;

  Z3_ast_vector poly = Z3_algebraic_get_poly(ctx, ast);
  if (poly == NULL) return FALSE;
  Z3_ast_vector_inc_ref(ctx, poly);
  term_t coeffs = PL_new_term_ref();
  PL_put_nil(coeffs);
  term_t coeff = PL_new_term_ref();
  for (unsigned i = Z3_ast_vector_size(ctx, poly); ok && i > 0; i--) { // build the list from the end
    ok = PL_put_variable(coeff)
      && z3_ast_to_term_internal(ctx, Z3_ast_vector_get(ctx, poly, i - 1), coeff)
      && PL_cons_list(coeffs, coeff, coeffs);
  }
  Z3_ast_vector_dec_ref(ctx, poly);
  if (!ok) return FALSE;

  unsigned index = Z3_algebraic_get_i(ctx, ast);
  term_t result = PL_new_term_ref();
  return PL_unify_term(result,
                       PL_FUNCTOR_CHARS, "algebraic", 2,
                         PL_FLOAT, approx,
                         PL_FUNCTOR_CHARS, "root", 2,
                           PL_TERM, coeffs,
                           PL_INT, (int) index)
    && PL_unify(term, result);
}

// A sort as written in formulas (see mk_sort): int, real, bool, string, bv(N), array(I, V), or the
// sort's name for enumeration and uninterpreted sorts.
static int prolog_sort_term(Z3_context ctx, Z3_sort sort, term_t term) {
  switch (Z3_get_sort_kind(ctx, sort)) {
  case Z3_INT_SORT:  return PL_put_atom_chars(term, "int");
  case Z3_REAL_SORT: return PL_put_atom_chars(term, "real");
  case Z3_BOOL_SORT: return PL_put_atom_chars(term, "bool");
  case Z3_FLOATING_POINT_SORT:
  case Z3_ROUNDING_MODE_SORT: return fp_sort_to_term(ctx, sort, term);
  case Z3_BV_SORT: {
    term_t width = PL_new_term_ref();
    return PL_put_int64(width, Z3_get_bv_sort_size(ctx, sort))
      && PL_cons_functor(term, PL_new_functor(PL_new_atom("bv"), 1), width);
  }
  case Z3_ARRAY_SORT: {
    term_t parts = PL_new_term_refs(2);
    return prolog_sort_term(ctx, Z3_get_array_sort_domain(ctx, sort), parts)
      && prolog_sort_term(ctx, Z3_get_array_sort_range(ctx, sort), parts + 1)
      && PL_cons_functor(term, PL_new_functor(PL_new_atom("array"), 2), parts, parts + 1);
  }
  default:
    if (Z3_is_string_sort(ctx, sort)) return PL_put_atom_chars(term, "string");
    return PL_put_atom_chars(term, Z3_get_symbol_string(ctx, Z3_get_sort_name(ctx, sort)));
  }
}

// The Prolog name of a Z3 operation whose Z3 name differs, or NULL: the string operations (see the
// str_ cases in compound_to_ast), which Z3 prints with SMT-LIB names such as str.len that Prolog code
// would have to quote, and the conversions Z3 inserts when integers and reals are mixed.
static const char *string_operation_name(Z3_decl_kind kind) {
  switch (kind) {
  case Z3_OP_SEQ_CONCAT:   return "str_concat";
  case Z3_OP_SEQ_LENGTH:   return "str_len";
  case Z3_OP_SEQ_EXTRACT:  return "str_substr";
  case Z3_OP_SEQ_AT:       return "str_at";
  case Z3_OP_SEQ_CONTAINS: return "str_contains";
  case Z3_OP_SEQ_PREFIX:   return "str_prefixof";
  case Z3_OP_SEQ_SUFFIX:   return "str_suffixof";
  case Z3_OP_SEQ_INDEX:    return "str_indexof";
  case Z3_OP_SEQ_REPLACE:  return "str_replace";
  case Z3_OP_STRING_LT:    return "str_lt";
  case Z3_OP_STRING_LE:    return "str_le";
  case Z3_OP_STR_TO_INT:   return "str_to_int";
  case Z3_OP_INT_TO_STR:   return "int_to_str";
  case Z3_OP_TO_REAL:      return "int2real";   // Z3: to_real
  case Z3_OP_TO_INT:       return "real2int";   // Z3: to_int
  // Floating point: Z3 prints fp.add and so on, and roundNearestTiesToEven for rne.
  case Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN: return "rne";
  case Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY: return "rna";
  case Z3_OP_FPA_RM_TOWARD_POSITIVE:      return "rtp";
  case Z3_OP_FPA_RM_TOWARD_NEGATIVE:      return "rtn";
  case Z3_OP_FPA_RM_TOWARD_ZERO:          return "rtz";
  case Z3_OP_FPA_ABS:      return "fp_abs";
  case Z3_OP_FPA_NEG:      return "fp_neg";
  case Z3_OP_FPA_ADD:      return "fp_add";
  case Z3_OP_FPA_SUB:      return "fp_sub";
  case Z3_OP_FPA_MUL:      return "fp_mul";
  case Z3_OP_FPA_DIV:      return "fp_div";
  case Z3_OP_FPA_FMA:      return "fp_fma";
  case Z3_OP_FPA_SQRT:     return "fp_sqrt";
  case Z3_OP_FPA_REM:      return "fp_rem";
  case Z3_OP_FPA_ROUND_TO_INTEGRAL: return "fp_round_to_integral";
  case Z3_OP_FPA_MIN:      return "fp_min";
  case Z3_OP_FPA_MAX:      return "fp_max";
  case Z3_OP_FPA_LE:       return "fp_leq";
  case Z3_OP_FPA_LT:       return "fp_lt";
  case Z3_OP_FPA_GE:       return "fp_geq";
  case Z3_OP_FPA_GT:       return "fp_gt";
  case Z3_OP_FPA_EQ:       return "fp_eq";
  case Z3_OP_FPA_IS_NORMAL:    return "fp_is_normal";
  case Z3_OP_FPA_IS_SUBNORMAL: return "fp_is_subnormal";
  case Z3_OP_FPA_IS_ZERO:      return "fp_is_zero";
  case Z3_OP_FPA_IS_INF:       return "fp_is_infinite";
  case Z3_OP_FPA_IS_NAN:       return "fp_is_nan";
  case Z3_OP_FPA_IS_NEGATIVE:  return "fp_is_negative";
  case Z3_OP_FPA_IS_POSITIVE:  return "fp_is_positive";
  case Z3_OP_FPA_TO_REAL:      return "fp_to_real";
  case Z3_OP_FPA_TO_IEEE_BV:   return "fp_to_ieee_bv";
  default:                 return NULL;
  }
}

#define FP_DECIMAL_PLACES 1100 // a double's smallest subnormal, 2^-1074, has 1074 decimal places

/*
  A floating-point numeral as fp_value(Value, Sort), as accepted by term_to_ast. Value is nan, inf
  or -inf; or, for formats that fit in a double (at most 11 exponent and 53 significand bits, as
  float16, float32 and float64), a Prolog float with exactly the numeral's value, -0.0 included;
  or, for larger formats, the exact value as a Prolog integer or rational.
*/
static int fp_value_to_term(const Z3_context ctx, Z3_ast ast, term_t term) {
  Z3_sort sort = Z3_get_sort(ctx, ast);
  term_t args = PL_new_term_refs(2);
  if (!fp_sort_to_term(ctx, sort, args + 1)) return FALSE;
  int ok;
  if (Z3_fpa_is_numeral_nan(ctx, ast)) {
    ok = PL_put_atom_chars(args, "nan");
  }
  else if (Z3_fpa_is_numeral_inf(ctx, ast)) {
    ok = PL_put_atom_chars(args, "inf");
    if (ok && Z3_fpa_is_numeral_negative(ctx, ast)) {
      ok = PL_cons_functor(args, PL_new_functor(PL_new_atom("-"), 1), args);
    }
  }
  else if (Z3_fpa_is_numeral_zero(ctx, ast)) {
    ok = PL_put_float(args, Z3_fpa_is_numeral_negative(ctx, ast) ? -0.0 : 0.0);
  }
  else {
    Z3_ast real = Z3_simplify(ctx, Z3_mk_fpa_to_real(ctx, ast));
    if (real == NULL || !Z3_is_numeral_ast(ctx, real)) {
      ERROR("could not convert floating-point numeral %s\n", Z3_ast_to_string(ctx, ast));
      return FALSE;
    }
    if (Z3_fpa_get_ebits(ctx, sort) <= 11 && Z3_fpa_get_sbits(ctx, sort) <= 53) {
      // The value is a double, and its decimal expansion is finite, so strtod gives it exactly.
      Z3_string digits = Z3_get_numeral_decimal_string(ctx, real, FP_DECIMAL_PLACES);
      ok = PL_put_float(args, strtod(digits, NULL));
    }
    else {
      char *num = strdup(Z3_get_numeral_string(ctx, Z3_get_numerator(ctx, real)));
      char *den = strdup(Z3_get_numeral_string(ctx, Z3_get_denominator(ctx, real)));
      if (num == NULL || den == NULL) { free(num); free(den); return PL_resource_error("memory"); }
      size_t n = strlen(num) + strlen(den) + 2;
      char *text = malloc(n);
      if (text == NULL) { free(num); free(den); return PL_resource_error("memory"); }
      if (strcmp(den, "1") == 0) snprintf(text, n, "%s", num);
      else snprintf(text, n, "%sr%s", num, den);           // Prolog rational syntax, as in 1r3
      ok = PL_chars_to_term(text, args);
      free(num); free(den); free(text);
    }
  }
  term_t result = PL_new_term_ref();
  return ok && PL_cons_functor(result, PL_new_functor(PL_new_atom("fp_value"), 2), args, args + 1)
    && PL_unify(term, result);
}

/*
  Floating-point conversions whose result sort or width is a parameter of the Z3 operation, not an
  argument, as accepted by term_to_ast: to_fp(RM, X, Sort), to_fp_unsigned(RM, BV, Sort),
  fp_from_ieee_bv(BV, Sort), fp_to_sbv(RM, X, Width) and fp_to_ubv(RM, X, Width). subterms are the
  converted arguments. Returns -1 if ast is none of these.
*/
static int fp_conversion_to_term(const Z3_context ctx, Z3_ast ast, Z3_decl_kind kind, unsigned arity,
                                 term_t subterms, term_t term) {
  const char *name;
  switch (kind) {
  case Z3_OP_FPA_TO_FP:          name = arity == 1 ? "fp_from_ieee_bv" : "to_fp"; break;
  case Z3_OP_FPA_TO_FP_UNSIGNED: name = "to_fp_unsigned"; break;
  case Z3_OP_FPA_TO_SBV:         name = "fp_to_sbv"; break;
  case Z3_OP_FPA_TO_UBV:         name = "fp_to_ubv"; break;
  default: return -1;
  }
  term_t args = PL_new_term_refs(arity + 1);
  for (unsigned i = 0; i < arity; i++) {
    if (!PL_put_term(args + i, subterms + i)) return FALSE;
  }
  Z3_sort sort = Z3_get_sort(ctx, ast);
  int ok = (kind == Z3_OP_FPA_TO_SBV || kind == Z3_OP_FPA_TO_UBV)
    ? PL_put_int64(args + arity, Z3_get_bv_sort_size(ctx, sort))
    : fp_sort_to_term(ctx, sort, args + arity);
  term_t result = PL_new_term_ref();
  return ok && PL_cons_functor_v(result, PL_new_functor(PL_new_atom(name), arity + 1), args)
    && PL_unify(term, result);
}

/*
  While converting a quantifier's body back to Prolog, the names of the variables it binds, innermost
  quantifier first. Z3 refers to a bound variable by a de Bruijn index: 0 is the last variable of
  the innermost quantifier, then the ones before it, then the outer quantifiers' variables.
*/
struct scope {
  const struct scope *outer;
  unsigned num_names;
  atom_t *names;
  bool *used;      // if not NULL, set when one of the names is used
};

static foreign_t ast_to_term_scoped(const Z3_context ctx, Z3_ast ast, term_t term, const struct scope *scope);

foreign_t z3_ast_to_term_internal(const Z3_context ctx, Z3_ast ast, term_t term) {
  return ast_to_term_scoped(ctx, ast, term, NULL);
}

// forall(Vars, Body) or exists(Vars, Body), Vars a list of Name:Sort, as accepted by term_to_ast.
static foreign_t quantifier_to_term(const Z3_context ctx, Z3_ast ast, term_t term, const struct scope *outer) {
  if (Z3_is_lambda(ctx, ast)) {
    INFO("z3_ast_to_term: lambda terms are not supported\n");
    return FALSE;
  }
  unsigned n = Z3_get_quantifier_num_bound(ctx, ast);
  atom_t *names = malloc((n > 0 ? n : 1) * sizeof(atom_t));
  if (names == NULL) return PL_resource_error("memory");
  term_t vars = PL_new_term_ref(), var = PL_new_term_ref(), sort = PL_new_term_ref(), name = PL_new_term_ref();
  PL_put_nil(vars);
  int ok = TRUE;
  for (unsigned i = 0; i < n; i++) {
    names[i] = PL_new_atom(Z3_get_symbol_string(ctx, Z3_get_quantifier_bound_name(ctx, ast, i)));
  }
  for (unsigned i = n; ok && i > 0; i--) { // build the list from the end
    PL_put_atom(name, names[i - 1]);
    ok = prolog_sort_term(ctx, Z3_get_quantifier_bound_sort(ctx, ast, i - 1), sort)
      && PL_cons_functor(var, PL_new_functor(PL_new_atom(":"), 2), name, sort)
      && PL_cons_list(vars, var, vars);
  }
  struct scope inner = { .outer = outer, .num_names = n, .names = names, .used = NULL };
  term_t body = PL_new_term_ref();
  ok = ok && ast_to_term_scoped(ctx, Z3_get_quantifier_body(ctx, ast), body, &inner);
  term_t result = PL_new_term_ref();
  const char *q = Z3_is_quantifier_forall(ctx, ast) ? "forall" : "exists";
  ok = ok && PL_cons_functor(result, PL_new_functor(PL_new_atom(q), 2), vars, body)
          && PL_unify(term, result);
  for (unsigned i = 0; i < n; i++) PL_unregister_atom(names[i]);
  free(names);
  return ok;
}

// A bound variable: its name, found from its de Bruijn index in the enclosing scopes.
static foreign_t variable_to_term(const Z3_context ctx, Z3_ast ast, term_t term, const struct scope *scope) {
  unsigned index = Z3_get_index_value(ctx, ast);
  for (; scope != NULL; scope = scope->outer) {
    if (index < scope->num_names) {
      if (scope->used != NULL) *scope->used = true;
      return PL_unify_atom(term, scope->names[scope->num_names - 1 - index]);
    }
    index -= scope->num_names;
  }
  INFO("z3_ast_to_term: a bound variable outside any quantifier\n");
  return FALSE;
}

static foreign_t ast_to_term_scoped(const Z3_context ctx, Z3_ast ast, term_t term, const struct scope *scope) {
  if (Z3_get_ast_kind(ctx, ast) == Z3_QUANTIFIER_AST) {
    return quantifier_to_term(ctx, ast, term, scope);
  }
  if (Z3_get_ast_kind(ctx, ast) == Z3_VAR_AST) {
    return variable_to_term(ctx, ast, term, scope);
  }
  if (Z3_is_app(ctx, ast)   // a numeral is an app too, of ast kind Z3_NUMERAL_AST
      && Z3_get_sort_kind(ctx, Z3_get_sort(ctx, ast)) == Z3_ROUNDING_MODE_SORT) {
    // A rounding-mode value, such as rne. Z3 counts these as numerals, without a numeric value.
    const char *name = string_operation_name(Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ast))));
    if (name != NULL) return PL_unify_atom_chars(term, name);
  }
  if (Z3_is_app(ctx, ast)
      && Z3_get_sort_kind(ctx, Z3_get_sort(ctx, ast)) == Z3_FLOATING_POINT_SORT) {
    switch (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ast)))) {
    case Z3_OP_FPA_NUM: case Z3_OP_FPA_NAN: case Z3_OP_FPA_PLUS_INF: case Z3_OP_FPA_MINUS_INF:
    case Z3_OP_FPA_PLUS_ZERO: case Z3_OP_FPA_MINUS_ZERO:
      return fp_value_to_term(ctx, ast, term);
    default:
      break;
    }
  }
  if (Z3_is_algebraic_number(ctx, ast)) {
    return algebraic_to_term(ctx, ast, term);
  }
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
    // By code point, the inverse of the conversion in term_to_ast; Z3_get_string would escape
    // backslashes and non-ASCII characters.
    unsigned len = Z3_get_string_length(ctx, ast);
    unsigned *code_points = malloc((len > 0 ? len : 1) * sizeof(unsigned));
    pl_wchar_t *chars = malloc((len > 0 ? len : 1) * sizeof(pl_wchar_t));
    if (code_points == NULL || chars == NULL) {
      free(code_points); free(chars);
      return PL_resource_error("memory");
    }
    Z3_get_string_contents(ctx, ast, len, code_points);
    for (unsigned i = 0; i < len; i++) chars[i] = (pl_wchar_t) code_points[i];
    int ok = PL_unify_wchars(term, PL_STRING, len, chars);
    free(code_points); free(chars);
    return ok;
  }

  if (Z3_get_ast_kind(ctx, ast) == Z3_APP_AST) {
    Z3_app app = Z3_to_app(ctx, ast);
    const unsigned arity = Z3_get_app_num_args(ctx, app);
    DEBUG("We have a Z3_app_ast of arity %d\n", arity);
    term_t subterms = PL_new_term_refs(arity);
    for (int i=0; i<arity; ++i) {
      Z3_ast subterm_ast = Z3_get_app_arg(ctx, app, i);
      if (!ast_to_term_scoped(ctx, subterm_ast, subterms+i, scope)) {
        return FALSE;
      }
    }
    Z3_func_decl decl = Z3_get_app_decl(ctx, app);
    Z3_symbol symbol = Z3_get_decl_name(ctx, decl);
    term_t t = PL_new_term_ref();
    functor_t func;
    if (Z3_get_decl_kind(ctx, decl) == Z3_OP_CONST_ARRAY) {
      // const_array(IndexSort, Value), as accepted by term_to_ast; the sort is not an argument in Z3.
      term_t sort_and_value = PL_new_term_refs(2);
      return prolog_sort_term(ctx, Z3_get_array_sort_domain(ctx, Z3_get_sort(ctx, ast)), sort_and_value)
        && PL_put_term(sort_and_value + 1, subterms)
        && PL_cons_functor(t, PL_new_functor(PL_new_atom("const_array"), 2), sort_and_value, sort_and_value + 1)
        && PL_unify(term, t);
    }
    int conversion = fp_conversion_to_term(ctx, ast, Z3_get_decl_kind(ctx, decl), arity, subterms, term);
    if (conversion != -1) return conversion;
    const char *prolog_name = string_operation_name(Z3_get_decl_kind(ctx, decl));
    if (prolog_name != NULL) {
      func = PL_new_functor(PL_new_atom(prolog_name), arity);
    }
    else {
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
    // Like must_be(between(0, Scopes), N): error(domain_error(between(0, Scopes), N), _).
    term_t ex = PL_new_term_ref();
    if (!PL_unify_term(ex, PL_FUNCTOR_CHARS, "error", 2,
                             PL_FUNCTOR_CHARS, "domain_error", 2,
                               PL_FUNCTOR_CHARS, "between", 2, PL_INT, 0, PL_INT, scopes,
                               PL_TERM, npops,
                             PL_VARIABLE)) {
      return FALSE;
    }
    return PL_raise_exception(ex);
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
  DEBUG("Checking solver %p with context %p\n", h->solver, h->ctx);

  Z3_lbool check_status;
  if (!interruptible_check(h, &check_status)) return FALSE; // a signal raised an exception
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
  Z3_lbool check_status;
  if (!interruptible_check(h, &check_status)) return FALSE; // a signal raised an exception
  print_check_result(h->ctx, h->solver, check_status);
  return z3_lbool_to_atom(check_status, status_arg);
}

/*
  Sets the solver's timeout, in milliseconds: a check that takes longer returns l_undef, with reason
  timeout (see z3_reason_unknown/2). 0 removes the limit.
*/
static foreign_t z3_set_timeout_foreign_locked(handle h, term_t handle_term, term_t ms_term);

foreign_t z3_set_timeout_foreign(term_t handle_term, term_t ms_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_set_timeout_foreign_locked(h, handle_term, ms_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_set_timeout_foreign_locked(handle h, term_t handle_term, term_t ms_term) {
  (void) handle_term;
  int64_t ms;
  if (!PL_get_int64_ex(ms_term, &ms)) return FALSE;
  if (ms < 0 || ms >= UINT_MAX) {
    term_t ex = PL_new_term_ref();
    if (!PL_unify_term(ex, PL_FUNCTOR_CHARS, "error", 2,
                             PL_FUNCTOR_CHARS, "domain_error", 2,
                               PL_FUNCTOR_CHARS, "between", 2, PL_INT, 0, PL_INT64, (int64_t) UINT_MAX - 1,
                               PL_TERM, ms_term,
                             PL_VARIABLE)) return FALSE;
    return PL_raise_exception(ex);
  }
  Z3_context ctx = h->ctx;
  Z3_params params = Z3_mk_params(ctx);
  Z3_params_inc_ref(ctx, params);
  // Z3 has no explicit "no timeout" value; its default is the largest unsigned.
  Z3_params_set_uint(ctx, params, Z3_mk_string_symbol(ctx, "timeout"), ms == 0 ? UINT_MAX : (unsigned) ms);
  Z3_solver_set_params(ctx, h->solver, params);
  h->timeout_ms = (unsigned) ms;
  Z3_params_dec_ref(ctx, params);
  return TRUE;
}

/* Why the last check returned l_undef, as an atom such as timeout, interrupted or canceled. */
static foreign_t z3_reason_unknown_foreign_locked(handle h, term_t handle_term, term_t reason_term);

foreign_t z3_reason_unknown_foreign(term_t handle_term, term_t reason_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_reason_unknown_foreign_locked(h, handle_term, reason_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_reason_unknown_foreign_locked(handle h, term_t handle_term, term_t reason_term) {
  (void) handle_term;
  return PL_unify_atom_chars(reason_term, Z3_solver_get_reason_unknown(h->ctx, h->solver));
}

/*
  Interrupts a check running on handle_term, normally from another thread; the check then returns
  l_undef with reason interrupted. Does nothing if no check is running. It does not take the handle's
  lock, since the point is to reach a handle that is busy; pending_lock keeps the context from being
  deleted meanwhile. Z3_interrupt is designed to be called while another thread uses the context.
*/
foreign_t z3_interrupt_foreign(term_t handle_term) {
  void *data;
  PL_blob_t *type;
  if (!PL_get_blob(handle_term, &data, NULL, &type) || type != &z3_handle_blob) {
    if (PL_is_variable(handle_term)) return PL_instantiation_error(handle_term);
    return PL_type_error("z3_handle", handle_term);
  }
  handle h = data;
  int live;
  pthread_mutex_lock(&h->pending_lock);
  live = h->ctx != NULL;
  if (live) Z3_interrupt(h->ctx);
  pthread_mutex_unlock(&h->pending_lock);
  return live ? TRUE : PL_existence_error("z3_handle", handle_term);
}

// True if a is a Boolean literal: an uninterpreted Boolean constant, or its negation.
static int boolean_literal(Z3_context ctx, Z3_ast a) {
  if (Z3_get_ast_kind(ctx, a) != Z3_APP_AST || Z3_get_sort_kind(ctx, Z3_get_sort(ctx, a)) != Z3_BOOL_SORT) return FALSE;
  Z3_app app = Z3_to_app(ctx, a);
  Z3_func_decl decl = Z3_get_app_decl(ctx, app);
  if (Z3_get_decl_kind(ctx, decl) == Z3_OP_NOT) return boolean_literal(ctx, Z3_get_app_arg(ctx, app, 0));
  return Z3_get_decl_kind(ctx, decl) == Z3_OP_UNINTERPRETED && Z3_get_app_num_args(ctx, app) == 0;
}

/*
  Checks the solver's assertions under extra assumptions, which must be Boolean literals: Boolean
  constants such as p:bool, or their negations. They hold for this check only. After l_false,
  z3_get_unsat_core/2 gives the assumptions the proof of unsatisfiability used. Interruptible, like z3_check.
  Raises domain_error(boolean_literal, A) for an assumption A that is not a literal.
*/
static foreign_t z3_check_assumptions_foreign_locked(handle h, term_t handle_term, term_t list, term_t status_term);

foreign_t z3_check_assumptions_foreign(term_t handle_term, term_t list, term_t status_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_check_assumptions_foreign_locked(h, handle_term, list, status_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_check_assumptions_foreign_locked(handle h, term_t handle_term, term_t list, term_t status_term) {
  (void) handle_term;
  size_t n;
  switch (PL_skip_list(list, 0, &n)) {
  case PL_LIST: break;
  case PL_PARTIAL_LIST: return PL_instantiation_error(list);
  default: return PL_type_error("list", list);
  }
  if (!PL_is_ground(list)) return PL_instantiation_error(list);
  Z3_ast *assumptions = malloc((n > 0 ? n : 1) * sizeof(Z3_ast));
  if (assumptions == NULL) return PL_resource_error("memory");
  term_t head = PL_new_term_ref(), tail = PL_copy_term_ref(list);
  size_t i = 0;
  while (PL_get_list(tail, head, tail)) {
    Z3_ast a = term_to_ast(h, h->declarations, head);
    if (a == NULL || !boolean_literal(h->ctx, a)) {
      free(assumptions);
      return a == NULL && PL_exception(0) ? FALSE : PL_domain_error("boolean_literal", head);
    }
    assumptions[i++] = a;
  }
  Z3_lbool status;
  int ok = interruptible_check_assumptions(h, (unsigned) n, assumptions, &status);
  free(assumptions);
  if (!ok) return FALSE; // a signal raised an exception
  return z3_lbool_to_atom(status, status_term);
}

/*
  The unsat core of the last check: after z3_check_assumptions/3 returned l_false, the assumptions
  its proof used, as a list of literals. Z3 makes cores small, but they need not be minimal.
*/
static foreign_t z3_get_unsat_core_foreign_locked(handle h, term_t handle_term, term_t core_term);

foreign_t z3_get_unsat_core_foreign(term_t handle_term, term_t core_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_get_unsat_core_foreign_locked(h, handle_term, core_term);
  unlock_handle(h);
  return locked_rval;
}

static foreign_t z3_get_unsat_core_foreign_locked(handle h, term_t handle_term, term_t core_term) {
  (void) handle_term;
  Z3_context ctx = h->ctx;
  Z3_ast_vector core = Z3_solver_get_unsat_core(ctx, h->solver);
  if (core == NULL) return FALSE;
  Z3_ast_vector_inc_ref(ctx, core);
  term_t list = PL_new_term_ref();
  PL_put_nil(list);
  term_t elem = PL_new_term_ref();
  int ok = TRUE;
  for (unsigned i = Z3_ast_vector_size(ctx, core); ok && i > 0; i--) { // build the list from the end
    ok = PL_put_variable(elem)
      && z3_ast_to_term_internal(ctx, Z3_ast_vector_get(ctx, core, i - 1), elem)
      && PL_cons_list(list, elem, list);
  }
  Z3_ast_vector_dec_ref(ctx, core);
  return ok && PL_unify(core_term, list);
}

/*
  One-shot optimization. Creates a Z3 optimizer, asserts the solver's assertions in it, and adds
  the Objectives, in priority order (lexicographic, Z3's default):
    minimize(T), maximize(T)   an arithmetic or bit-vector term T;
    soft(F), soft(F, Weight)   a formula F that should hold, with a positive integer or float Weight
                               (1 by default). All soft constraints together form one objective, at
                               the position of the first one, minimizing the total weight violated.
  Status is the check's status. After l_true, Values has one value per objective, in order: the
  optimum of T, or for soft(F, ...) whether F holds in the model; and Model is a model blob, as from
  z3_get_model/2. Otherwise Values is [] and Model is none. An optimum can be infinite or not
  attained: values can contain oo (infinity) and epsilon (an infinitesimal), as in -1*oo for an
  unbounded minimum, or epsilon for the infimum of x > 0. The optimizer is freed before returning.
  The check is interruptible, like z3_check, and uses the timeout from z3_set_timeout/2.
  Raises domain_error(z3_objective, O) for an objective of another form, and domain_error for a
  weight that is not positive.
*/
enum objective_kind { OBJECTIVE_MINIMIZE, OBJECTIVE_MAXIMIZE, OBJECTIVE_SOFT };

struct objective {
  enum objective_kind kind;
  unsigned index;   // from Z3_optimize_minimize/maximize
  Z3_ast formula;   // the soft constraint
};

static foreign_t z3_optimize_foreign_locked(handle h, term_t handle_term, term_t objectives,
                                            term_t status_term, term_t values_term, term_t model_term);

foreign_t z3_optimize_foreign(term_t handle_term, term_t objectives, term_t status_term, term_t values_term, term_t model_term) {
  handle h;
  if (!lock_handle(handle_term, &h)) return FALSE;
  foreign_t locked_rval = z3_optimize_foreign_locked(h, handle_term, objectives, status_term, values_term, model_term);
  unlock_handle(h);
  return locked_rval;
}

// Adds one objective term to o, filling in *obj. FALSE, with an exception or a printed message, if it is bad.
static int add_objective(handle h, Z3_optimize o, term_t objective, struct objective *obj) {
  Z3_context ctx = h->ctx;
  atom_t name;
  size_t arity;
  if (!PL_get_name_arity(objective, &name, &arity)) {
    return PL_domain_error("z3_objective", objective);
  }
  const char *n = PL_atom_nchars(name, NULL);
  term_t arg = PL_new_term_ref();
  if ((strcmp(n, "minimize") == 0 || strcmp(n, "maximize") == 0) && arity == 1) {
    if (!PL_get_arg(1, objective, arg)) return FALSE;
    Z3_ast t = term_to_ast(h, h->declarations, arg);
    if (t == NULL) return FALSE;
    Z3_sort_kind k = Z3_get_sort_kind(ctx, Z3_get_sort(ctx, t));
    if (k != Z3_INT_SORT && k != Z3_REAL_SORT && k != Z3_BV_SORT) {
      ERROR("%s: the objective should be an arithmetic or bit-vector term\n", n);
      return FALSE;
    }
    obj->kind = n[1] == 'i' ? OBJECTIVE_MINIMIZE : OBJECTIVE_MAXIMIZE;
    obj->index = obj->kind == OBJECTIVE_MINIMIZE ? Z3_optimize_minimize(ctx, o, t) : Z3_optimize_maximize(ctx, o, t);
    return TRUE;
  }
  if (strcmp(n, "soft") == 0 && (arity == 1 || arity == 2)) {
    if (!PL_get_arg(1, objective, arg)) return FALSE;
    Z3_ast f = term_to_ast(h, h->declarations, arg);
    if (f == NULL) return FALSE;
    if (Z3_get_sort_kind(ctx, Z3_get_sort(ctx, f)) != Z3_BOOL_SORT) {
      ERROR("soft: the constraint should be a formula\n");
      return FALSE;
    }
    char *weight = "1";
    if (arity == 2) {
      term_t w = PL_new_term_ref();
      double d;
      if (!PL_get_arg(2, objective, w)) return FALSE;
      if (!(PL_is_integer(w) || PL_is_float(w))) return PL_type_error("number", w);
      if (!PL_get_float(w, &d) || !(d > 0)) return PL_domain_error("positive_number", w);
      if (!PL_get_chars(w, &weight, CVT_INTEGER | CVT_FLOAT)) return FALSE;
    }
    obj->kind = OBJECTIVE_SOFT;
    obj->formula = f;
    Z3_optimize_assert_soft(ctx, o, f, weight, Z3_mk_string_symbol(ctx, "soft"));
    return TRUE;
  }
  return PL_domain_error("z3_objective", objective);
}

static foreign_t z3_optimize_foreign_locked(handle h, term_t handle_term, term_t objectives,
                                            term_t status_term, term_t values_term, term_t model_term) {
  (void) handle_term;
  Z3_context ctx = h->ctx;
  size_t n;
  switch (PL_skip_list(objectives, 0, &n)) {
  case PL_LIST: break;
  case PL_PARTIAL_LIST: return PL_instantiation_error(objectives);
  default: return PL_type_error("list", objectives);
  }
  if (!require_ground(objectives)) return FALSE;

  Z3_optimize o = Z3_mk_optimize(ctx);
  Z3_optimize_inc_ref(ctx, o);
  if (h->timeout_ms != 0) {
    Z3_params params = Z3_mk_params(ctx);
    Z3_params_inc_ref(ctx, params);
    Z3_params_set_uint(ctx, params, Z3_mk_string_symbol(ctx, "timeout"), h->timeout_ms);
    Z3_optimize_set_params(ctx, o, params);
    Z3_params_dec_ref(ctx, params);
  }
  Z3_ast_vector assertions = Z3_solver_get_assertions(ctx, h->solver);
  Z3_ast_vector_inc_ref(ctx, assertions);
  for (unsigned i = 0; i < Z3_ast_vector_size(ctx, assertions); i++) {
    Z3_optimize_assert(ctx, o, Z3_ast_vector_get(ctx, assertions, i));
  }
  Z3_ast_vector_dec_ref(ctx, assertions);

  struct objective *objs = malloc((n > 0 ? n : 1) * sizeof(struct objective));
  int ok = objs != NULL;
  if (!ok) PL_resource_error("memory");
  term_t head = PL_new_term_ref(), tail = PL_copy_term_ref(objectives);
  for (size_t i = 0; ok && PL_get_list(tail, head, tail); i++) {
    ok = add_objective(h, o, head, &objs[i]);
  }

  Z3_lbool status = Z3_L_UNDEF;
  if (ok) ok = interruptible_optimize(h, o, &status); // FALSE: a signal raised an exception

  term_t values = PL_new_term_ref();
  term_t model = PL_new_term_ref();
  PL_put_nil(values);
  if (ok && status == Z3_L_TRUE) {
    Z3_model m = Z3_optimize_get_model(ctx, o);
    term_t value = PL_new_term_ref();
    for (size_t i = n; ok && i > 0; i--) { // build the list from the end
      struct objective *obj = &objs[i - 1];
      ok = PL_put_variable(value);
      if (obj->kind == OBJECTIVE_SOFT) {
        Z3_ast holds;
        ok = ok && Z3_model_eval(ctx, m, obj->formula, true, &holds)
                && z3_ast_to_term_internal(ctx, holds, value);
      }
      else {
        Z3_ast bound = obj->kind == OBJECTIVE_MINIMIZE ? Z3_optimize_get_lower(ctx, o, obj->index)
                                                       : Z3_optimize_get_upper(ctx, o, obj->index);
        ok = ok && z3_ast_to_term_internal(ctx, bound, value);
      }
      ok = ok && PL_cons_list(values, value, values);
    }
    if (ok) {
      // A model blob, as in z3_get_model; it keeps a reference to h, and outlives the optimizer.
      model_ref mr = malloc(sizeof(struct ModelStruct));
      ok = mr != NULL;
      if (!ok) PL_resource_error("memory");
      else {
        Z3_model_inc_ref(ctx, m);
        mr->model = m;
        mr->h = h;
        atomic_fetch_add(&h->refcount, 1);
        ok = PL_unify_blob(model, mr, sizeof(*mr), &z3_model_blob);
      }
    }
  }
  else if (ok) {
    ok = PL_put_atom_chars(model, "none");
  }
  free(objs);
  Z3_optimize_dec_ref(ctx, o);
  return ok
    && z3_lbool_to_atom(status, status_term)
    && PL_unify(values_term, values)
    && PL_unify(model_term, model);
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


/*
  The else value of a function interpretation. It may depend on the arguments, which Z3 represents
  by bound variables: (:var 0) is the first argument (unlike in a quantifier body, where it is the
  last bound variable). Then it is lambda(Args, Body), with Args the arguments as Name:Sort, named
  x!0, x!1, ... as Z3 prints them; for example lambda(['x!0':int, 'x!1':int], 'x!0' - 'x!1').
  Otherwise it is the value itself.
*/
static foreign_t else_to_term(Z3_context ctx, Z3_func_decl fdecl, Z3_ast felse, term_t term) {
  unsigned n = Z3_get_domain_size(ctx, fdecl);
  atom_t *names = malloc((n > 0 ? n : 1) * sizeof(atom_t));
  if (names == NULL) return PL_resource_error("memory");
  for (unsigned i = 0; i < n; i++) {   // reversed, as variable_to_term counts from the last name
    char name[32];
    snprintf(name, sizeof name, "x!%u", n - 1 - i);
    names[i] = PL_new_atom(name);
  }
  bool used = false;
  struct scope args = { .outer = NULL, .num_names = n, .names = names, .used = &used };
  term_t body = PL_new_term_ref();
  int ok = ast_to_term_scoped(ctx, felse, body, &args);
  if (ok && !used) {
    ok = PL_unify(term, body);
  }
  else if (ok) {
    term_t vars = PL_new_term_ref(), var = PL_new_term_ref(), sort = PL_new_term_ref(), name = PL_new_term_ref();
    PL_put_nil(vars);
    for (unsigned k = n; ok && k > 0; k--) { // argument k - 1, building the list from the end
      ok = PL_put_atom(name, names[n - k])
        && prolog_sort_term(ctx, Z3_get_domain(ctx, fdecl, k - 1), sort)
        && PL_cons_functor(var, PL_new_functor(PL_new_atom(":"), 2), name, sort)
        && PL_cons_list(vars, var, vars);
    }
    term_t lambda = PL_new_term_ref();
    ok = ok && PL_cons_functor(lambda, PL_new_functor(PL_new_atom("lambda"), 2), vars, body)
            && PL_unify(term, lambda);
  }
  for (unsigned i = 0; i < n; i++) PL_unregister_atom(names[i]);
  free(names);
  return ok;
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
    if (!else_to_term(ctx, fdecl, felse, else_value)) {
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
    if (strcmp(name_string, "real") == 0) {
      return h->real_sort;
    }
    // float and double once meant real, which is not IEEE floating point; they are now errors, so that
    // neither meaning is assumed.
    if (strcmp(name_string, "float") == 0 || strcmp(name_string, "double") == 0) {
      ERROR("%s is not a sort: use real, or IEEE floating point float16, float32, float64, float128 or fp(Ebits, Sbits)\n", name_string);
      return NULL;
    }
    if (strcmp(name_string, "string") == 0) {
      return h->string_sort;
    }
    // IEEE floating point (see also fp(Ebits, Sbits) below), and the sort of rounding modes:
    if (strcmp(name_string, "float16") == 0)  return Z3_mk_fpa_sort_16(ctx);
    if (strcmp(name_string, "float32") == 0)  return Z3_mk_fpa_sort_32(ctx);
    if (strcmp(name_string, "float64") == 0)  return Z3_mk_fpa_sort_64(ctx);
    if (strcmp(name_string, "float128") == 0) return Z3_mk_fpa_sort_128(ctx);
    if (strcmp(name_string, "roundingmode") == 0) return Z3_mk_fpa_rounding_mode_sort(ctx);
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

    int res;

    atom_t name;
    size_t arity;
    res = PL_get_name_arity(expression, &name, &arity);
    if (!res) {
      ERROR("PL_get_name_arity failed\n");
      return FALSE;
    }

    const char *name_string = PL_atom_nchars(name, NULL);
    // INFO("sort expression %s has arity %lu\n", name_string, arity);

    if (strcmp(name_string, "array") == 0) { // array(IndexSort, ValueSort)
      CHECK_ARITY(name_string, 2, arity);
      term_t index = PL_new_term_ref(), value = PL_new_term_ref();
      if (!PL_get_arg(1, expression, index) || !PL_get_arg(2, expression, value)) return NULL;
      Z3_sort index_sort = mk_sort(h, index);
      if (index_sort == NULL) return NULL;
      Z3_sort value_sort = mk_sort(h, value);
      if (value_sort == NULL) return NULL;
      return Z3_mk_array_sort(ctx, index_sort, value_sort);
    }
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
    if (strcmp(name_string, "fp") == 0) { // fp(Ebits, Sbits): IEEE floating point; float32 is fp(8, 24)
      CHECK_ARITY(name_string, 2, arity);
      term_t e = PL_new_term_ref(), s = PL_new_term_ref();
      int ebits, sbits;
      if (!PL_get_arg(1, expression, e) || !PL_get_arg(2, expression, s)) return NULL;
      if (!PL_get_integer_ex(e, &ebits) || !PL_get_integer_ex(s, &sbits)) return NULL;
      if (ebits < 2 || sbits < 3) { // Z3's limits; sbits counts the hidden bit
        ERROR("fp(Ebits, Sbits) needs Ebits >= 2 and Sbits >= 3, got fp(%d, %d)\n", ebits, sbits);
        return NULL;
      }
      return Z3_mk_fpa_sort(ctx, (unsigned) ebits, (unsigned) sbits);
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

/*
  The floating-point operations, with the SMT-LIB argument orders (the rounding mode first). Sets
  *result (NULL on a Z3 error, such as a badly sorted argument) and returns true if name is one of
  them with this arity; false otherwise. fp_to_sbv and the other conversions with a sort or width
  argument are in fp_conversion_from_term.
*/
static bool fp_operation(Z3_context ctx, const char *name, size_t arity, Z3_ast *a, Z3_ast *result) {
  typedef Z3_ast (*unary)(Z3_context, Z3_ast);
  typedef Z3_ast (*binary)(Z3_context, Z3_ast, Z3_ast);
  typedef Z3_ast (*ternary)(Z3_context, Z3_ast, Z3_ast, Z3_ast);
  static const struct { const char *name; unary f; } unaries[] = {
    {"fp_abs", Z3_mk_fpa_abs}, {"fp_neg", Z3_mk_fpa_neg},
    {"fp_is_normal", Z3_mk_fpa_is_normal}, {"fp_is_subnormal", Z3_mk_fpa_is_subnormal},
    {"fp_is_zero", Z3_mk_fpa_is_zero}, {"fp_is_infinite", Z3_mk_fpa_is_infinite},
    {"fp_is_nan", Z3_mk_fpa_is_nan}, {"fp_is_negative", Z3_mk_fpa_is_negative},
    {"fp_is_positive", Z3_mk_fpa_is_positive},
    {"fp_to_real", Z3_mk_fpa_to_real}, {"fp_to_ieee_bv", Z3_mk_fpa_to_ieee_bv},
  };
  static const struct { const char *name; binary f; } binaries[] = {
    {"fp_rem", Z3_mk_fpa_rem}, {"fp_min", Z3_mk_fpa_min}, {"fp_max", Z3_mk_fpa_max},
    {"fp_leq", Z3_mk_fpa_leq}, {"fp_lt", Z3_mk_fpa_lt}, {"fp_geq", Z3_mk_fpa_geq},
    {"fp_gt", Z3_mk_fpa_gt}, {"fp_eq", Z3_mk_fpa_eq},
    {"fp_sqrt", Z3_mk_fpa_sqrt}, {"fp_round_to_integral", Z3_mk_fpa_round_to_integral}, // (rm, x)
  };
  static const struct { const char *name; ternary f; } ternaries[] = { // (rm, x, y)
    {"fp_add", Z3_mk_fpa_add}, {"fp_sub", Z3_mk_fpa_sub},
    {"fp_mul", Z3_mk_fpa_mul}, {"fp_div", Z3_mk_fpa_div},
  };
  if (arity == 1) {
    for (size_t i = 0; i < sizeof unaries / sizeof unaries[0]; i++)
      if (strcmp(name, unaries[i].name) == 0) { *result = unaries[i].f(ctx, a[0]); return true; }
  }
  else if (arity == 2) {
    for (size_t i = 0; i < sizeof binaries / sizeof binaries[0]; i++)
      if (strcmp(name, binaries[i].name) == 0) { *result = binaries[i].f(ctx, a[0], a[1]); return true; }
  }
  else if (arity == 3) {
    for (size_t i = 0; i < sizeof ternaries / sizeof ternaries[0]; i++)
      if (strcmp(name, ternaries[i].name) == 0) { *result = ternaries[i].f(ctx, a[0], a[1], a[2]); return true; }
  }
  else if (arity == 4 && strcmp(name, "fp_fma") == 0) { // (rm, x, y, z): x * y + z, rounded once
    *result = Z3_mk_fpa_fma(ctx, a[0], a[1], a[2], a[3]);
    return true;
  }
  return false;
}

static Z3_ast compound_to_ast(const handle h, decl_map declaration_map, const char *name_string,
                              const size_t arity, Z3_ast *subterms) {
  const Z3_context ctx = h->ctx;
  Z3_ast result = NULL;

  if (strncmp(name_string, "fp_", 3) == 0 && fp_operation(ctx, name_string, arity, subterms, &result)) {
    return result;
  }

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
  else if (strcmp(name_string, "=") == 0 || strcmp(name_string, "==") == 0 || strcmp(name_string, "equals") == 0
           || strcmp(name_string, "equal") == 0) {
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
  // ********************************************* strings ****************************************/
  // Argument orders follow SMT-LIB (str.prefixof, str.contains, str.substr, ...).
  // ********************************************* arrays ****************************************/
  else if (strcmp(name_string, "select") == 0) { // (array, index)
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_select(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "store") == 0) { // (array, index, value): the array with index set to value
    CHECK_ARITY(name_string, 3, arity);
    result = Z3_mk_store(ctx, subterms[0], subterms[1], subterms[2]);
  }
  else if (strcmp(name_string, "str_concat") == 0) {
    if (arity < 1) return NULL;
    result = arity == 1 ? subterms[0] : Z3_mk_seq_concat(ctx, (unsigned) arity, subterms);
  }
  else if (strcmp(name_string, "str_len") == 0) {
    CHECK_ARITY(name_string, 1, arity);
    result = Z3_mk_seq_length(ctx, subterms[0]);
  }
  else if (strcmp(name_string, "str_substr") == 0) { // (s, offset, length)
    CHECK_ARITY(name_string, 3, arity);
    result = Z3_mk_seq_extract(ctx, subterms[0], subterms[1], subterms[2]);
  }
  else if (strcmp(name_string, "str_at") == 0) { // (s, index): the one-character string at index
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_seq_at(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_contains") == 0) { // (container, containee)
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_seq_contains(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_prefixof") == 0) { // (prefix, s)
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_seq_prefix(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_suffixof") == 0) { // (suffix, s)
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_seq_suffix(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_indexof") == 0) { // (s, substring, start): -1 if not found
    CHECK_ARITY(name_string, 3, arity);
    result = Z3_mk_seq_index(ctx, subterms[0], subterms[1], subterms[2]);
  }
  else if (strcmp(name_string, "str_replace") == 0) { // (s, from, to): the first occurrence
    CHECK_ARITY(name_string, 3, arity);
    result = Z3_mk_seq_replace(ctx, subterms[0], subterms[1], subterms[2]);
  }
  else if (strcmp(name_string, "str_lt") == 0) { // lexicographic
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_str_lt(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_le") == 0) {
    CHECK_ARITY(name_string, 2, arity);
    result = Z3_mk_str_le(ctx, subterms[0], subterms[1]);
  }
  else if (strcmp(name_string, "str_to_int") == 0) { // -1 if not a sequence of digits
    CHECK_ARITY(name_string, 1, arity);
    result = Z3_mk_str_to_int(ctx, subterms[0]);
  }
  else if (strcmp(name_string, "int_to_str") == 0) { // "" for negative numbers
    CHECK_ARITY(name_string, 1, arity);
    result = Z3_mk_int_to_str(ctx, subterms[0]);
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
  Converts algebraic(Approx, root(Coefficients, Index)), as algebraic_to_term produces, back to Z3:
  the Index-th smallest real root (counting from 1) of the polynomial with integer Coefficients,
  lowest degree first. Approx, a float approximation, is ignored. The formula is already ground.
  Like other malformed values inside a formula, a malformed term fails with a message: Coefficients
  must be a proper list of integers whose last (leading) one is not zero, and the polynomial must
  have at least Index real roots.
*/
static Z3_ast algebraic_from_term(const handle h, const term_t formula) {
  const Z3_context ctx = h->ctx;
  term_t approx = PL_new_term_ref(), root = PL_new_term_ref();
  term_t coeffs = PL_new_term_ref(), index_term = PL_new_term_ref();
  atom_t root_name;
  size_t root_arity;
  if (!PL_get_arg(1, formula, approx) || !PL_get_arg(2, formula, root)
      || !PL_get_name_arity(root, &root_name, &root_arity)
      || root_arity != 2 || strcmp(PL_atom_nchars(root_name, NULL), "root") != 0
      || !PL_get_arg(1, root, coeffs) || !PL_get_arg(2, root, index_term)) {
    ERROR("algebraic/2: expected algebraic(Approx, root(Coefficients, Index))\n");
    return NULL;
  }
  if (!PL_is_number(approx)) {
    ERROR("algebraic/2: the approximation should be a number\n");
    return NULL;
  }
  int index;
  if (!PL_get_integer(index_term, &index) || index < 1) {
    ERROR("algebraic/2: the root index should be a positive integer\n");
    return NULL;
  }
  size_t n;
  if (PL_skip_list(coeffs, 0, &n) != PL_LIST || n < 2) {
    ERROR("algebraic/2: the coefficients should be a list of at least two integers\n");
    return NULL;
  }

  // Build sum(c_k * x^k), where x is bound variable 0: Z3_algebraic_roots only accepts polynomials
  // in bound variables, not in constants.
  const Z3_sort real = h->real_sort;
  const Z3_ast x = Z3_mk_bound(ctx, 0, real);
  Z3_ast *terms = malloc(n * sizeof(Z3_ast));
  Z3_ast *powers = malloc(n * sizeof(Z3_ast)); // x repeated, for the products
  if (terms == NULL || powers == NULL) {
    free(terms); free(powers);
    PL_resource_error("memory");
    return NULL;
  }
  for (size_t k = 0; k < n; k++) powers[k] = x;
  term_t head = PL_new_term_ref(), tail = PL_copy_term_ref(coeffs);
  size_t nterms = 0;
  int leading_zero = FALSE;
  for (size_t k = 0; PL_get_list(tail, head, tail); k++) {
    char *digits;
    if (!PL_is_integer(head) || !PL_get_chars(head, &digits, CVT_INTEGER)) {
      ERROR("algebraic/2: the coefficients should be integers\n");
      free(terms); free(powers);
      return NULL;
    }
    int zero = strcmp(digits, "0") == 0;
    if (k == n - 1) leading_zero = zero;
    if (zero) continue;
    Z3_ast c = Z3_mk_numeral(ctx, digits, real);
    if (k == 0) {
      terms[nterms++] = c;
    }
    else {
      Z3_ast xk = k == 1 ? x : Z3_mk_mul(ctx, (unsigned) k, powers);
      Z3_ast factors[2] = { c, xk };
      terms[nterms++] = Z3_mk_mul(ctx, 2, factors);
    }
  }
  free(powers);
  if (leading_zero) {
    ERROR("algebraic/2: the last (leading) coefficient should not be zero\n");
    free(terms);
    return NULL;
  }
  Z3_ast poly = nterms == 1 ? terms[0] : Z3_mk_add(ctx, (unsigned) nterms, terms);
  free(terms);

  Z3_ast_vector roots = Z3_algebraic_roots(ctx, poly, 0, NULL);
  if (roots == NULL) {
    ERROR("algebraic/2: Z3 could not find the roots of the polynomial\n");
    return NULL;
  }
  Z3_ast_vector_inc_ref(ctx, roots);
  unsigned nroots = Z3_ast_vector_size(ctx, roots);
  Z3_ast result = NULL;
  if ((unsigned) index > nroots) {
    ERROR("algebraic/2: root %d requested, but the polynomial has %u real roots\n", index, nroots);
  }
  else {
    result = Z3_ast_vector_get(ctx, roots, (unsigned) index - 1);
    // The vector holds the only reference to the root; keep one so it outlives the vector. Like every
    // AST in this (not reference counted) context, it is then freed when the context is deleted.
    Z3_inc_ref(ctx, result);
  }
  Z3_ast_vector_dec_ref(ctx, roots);
  return result;
}

// The constant for a variable named by the atom t, if an enclosing quantifier binds it, or NULL.
// Innermost first, so an inner quantifier's variable shadows an outer one of the same name.
static Z3_ast bound_variable(const handle h, term_t t) {
  atom_t name;
  if (h->num_bound == 0 || !PL_get_atom(t, &name)) return NULL;
  for (size_t i = h->num_bound; i > 0; i--) {
    if (h->bound[i - 1].name == name) return h->bound[i - 1].constant;
  }
  return NULL;
}

/*
  forall(Vars, Body) and exists(Vars, Body): Vars is a list of Name:Sort, and Body a formula in which
  the names refer to the bound variables, shadowing any constants of the same names. Like other
  malformed formulas, a malformed quantifier fails with a message. (z3.pl infers the sorts of bound
  variables that have none, and passes them on.)
*/
static Z3_ast quantifier_from_term(const handle h, decl_map declaration_map, const term_t formula, int is_forall) {
  const Z3_context ctx = h->ctx;
  term_t vars = PL_new_term_ref(), body = PL_new_term_ref();
  size_t n;
  if (!PL_get_arg(1, formula, vars) || !PL_get_arg(2, formula, body)
      || PL_skip_list(vars, 0, &n) != PL_LIST || n == 0) {
    ERROR("forall/exists: expected a non-empty list of Name:Sort bound variables\n");
    return NULL;
  }
  Z3_app *apps = malloc(n * sizeof(Z3_app));
  if (apps == NULL) { PL_resource_error("memory"); return NULL; }
  size_t base = h->num_bound;
  term_t head = PL_new_term_ref(), tail = PL_copy_term_ref(vars), name = PL_new_term_ref(), sort_term = PL_new_term_ref();
  Z3_ast result = NULL;
  int ok = TRUE;
  for (size_t i = 0; ok && PL_get_list(tail, head, tail); i++) {
    atom_t functor_name; size_t functor_arity; char *chars; atom_t a;
    ok = PL_get_name_arity(head, &functor_name, &functor_arity) && functor_arity == 2
      && strcmp(PL_atom_nchars(functor_name, NULL), ":") == 0
      && PL_get_arg(1, head, name) && PL_get_arg(2, head, sort_term)
      && PL_get_atom(name, &a) && PL_get_atom_chars(name, &chars);
    if (!ok) { ERROR("forall/exists: each bound variable should be Name:Sort\n"); break; }
    Z3_sort sort = mk_sort(h, sort_term);
    if (sort == NULL) { ok = FALSE; break; }
    Z3_ast constant = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, chars), sort);
    apps[i] = Z3_to_app(ctx, constant);
    if (h->num_bound == h->max_bound) {
      size_t new_max = h->max_bound == 0 ? 8 : 2 * h->max_bound;
      struct bound_variable *grown = realloc(h->bound, new_max * sizeof(struct bound_variable));
      if (grown == NULL) { PL_resource_error("memory"); ok = FALSE; break; }
      h->bound = grown;
      h->max_bound = new_max;
    }
    h->bound[h->num_bound].name = a;
    h->bound[h->num_bound].constant = constant;
    h->num_bound++;
  }
  if (ok) {
    Z3_ast b = term_to_ast(h, declaration_map, body);
    if (b != NULL && Z3_get_sort_kind(ctx, Z3_get_sort(ctx, b)) != Z3_BOOL_SORT) {
      ERROR("forall/exists: the body should be a formula\n");
      b = NULL;
    }
    if (b != NULL) {
      result = is_forall ? Z3_mk_forall_const(ctx, 0, (unsigned) n, apps, 0, NULL, b)
                         : Z3_mk_exists_const(ctx, 0, (unsigned) n, apps, 0, NULL, b);
    }
  }
  h->num_bound = base; // out of scope, on every path
  free(apps);
  return result;
}

/*
  Converts the Prolog term "formula" to a Z3 AST.
  Returns NULL if it fails:
*/

// The floating-point sort for Sort, or NULL with an error message.
static Z3_sort fp_sort_from_term(const handle h, term_t sort_term, const char *where) {
  Z3_sort sort = mk_sort(h, sort_term);
  if (sort == NULL) return NULL;
  if (Z3_get_sort_kind(h->ctx, sort) != Z3_FLOATING_POINT_SORT) {
    ERROR("%s: %s is not a floating-point sort\n", where, Z3_sort_to_string(h->ctx, sort));
    return NULL;
  }
  return sort;
}

/*
  fp_value(Value, Sort): the value of the floating-point Sort nearest to Value (rounding to nearest,
  ties to even), so fp_value(0.1, float32) is C's 0.1f. Value is an integer, a float, a rational,
  nan, inf or -inf; -0.0 is negative zero. A float is taken as the decimal number it prints as,
  which for a value from a model is exactly that value.
*/
static Z3_ast fp_value_from_term(const handle h, decl_map declaration_map, const term_t formula) {
  const Z3_context ctx = h->ctx;
  term_t value = PL_new_term_ref(), sort_term = PL_new_term_ref();
  if (!PL_get_arg(1, formula, value) || !PL_get_arg(2, formula, sort_term)) return NULL;
  Z3_sort sort = fp_sort_from_term(h, sort_term, "fp_value");
  if (sort == NULL) return NULL;
  char *name;
  if (PL_get_atom_chars(value, &name)) {
    if (strcmp(name, "nan") == 0) return Z3_mk_fpa_nan(ctx, sort);
    if (strcmp(name, "inf") == 0) return Z3_mk_fpa_inf(ctx, sort, false);
  }
  if (PL_is_functor(value, PL_new_functor(PL_new_atom("-"), 1))) {
    term_t arg = PL_new_term_ref();
    if (PL_get_arg(1, value, arg) && PL_get_atom_chars(arg, &name) && strcmp(name, "inf") == 0) {
      return Z3_mk_fpa_inf(ctx, sort, true);
    }
  }
  if (PL_is_float(value)) {
    double d;
    if (!PL_get_float(value, &d)) return NULL;
    if (isnan(d)) return Z3_mk_fpa_nan(ctx, sort);
    if (isinf(d)) return Z3_mk_fpa_inf(ctx, sort, d < 0);
    if (d == 0.0) return Z3_mk_fpa_zero(ctx, sort, signbit(d)); // the real 0 has no sign
  }
  if (!PL_is_number(value)) {
    char *text;
    if (!PL_get_chars(value, &text, CVT_WRITE)) text = NULL;
    ERROR("fp_value: %s should be a number, nan, inf or -inf\n", text ? text : "the value");
    return NULL;
  }
  Z3_ast real = term_to_ast(h, declaration_map, value);
  if (real == NULL) return NULL;
  if (Z3_get_sort_kind(ctx, Z3_get_sort(ctx, real)) == Z3_INT_SORT) real = Z3_mk_int2real(ctx, real);
  return Z3_simplify(ctx, Z3_mk_fpa_to_fp_real(ctx, Z3_mk_fpa_rne(ctx), real, sort));
}

// The conversions with a sort or width argument, which term_to_ast handles before the arguments.
static bool is_fp_conversion(const char *name, size_t arity) {
  return (arity == 3 && (strcmp(name, "to_fp") == 0 || strcmp(name, "to_fp_unsigned") == 0
                         || strcmp(name, "fp_to_sbv") == 0 || strcmp(name, "fp_to_ubv") == 0))
    || (arity == 2 && strcmp(name, "fp_from_ieee_bv") == 0);
}

/*
  to_fp(RM, X, Sort): X, a real, integer, floating-point number or (signed) bit vector, as the
  floating-point Sort, rounded by RM. to_fp_unsigned(RM, BV, Sort): BV as an unsigned integer.
  fp_from_ieee_bv(BV, Sort): the floating-point number whose IEEE bits are BV.
  fp_to_sbv(RM, X, Width) and fp_to_ubv(RM, X, Width): X rounded to a signed or unsigned integer,
  as a bit vector of Width bits.
*/
static Z3_ast fp_conversion_from_term(const handle h, decl_map declaration_map, const char *name,
                                      const term_t formula) {
  const Z3_context ctx = h->ctx;
  term_t a = PL_new_term_refs(3);
  if (strcmp(name, "fp_from_ieee_bv") == 0) {
    if (!PL_get_arg(1, formula, a) || !PL_get_arg(2, formula, a + 1)) return NULL;
    Z3_sort sort = fp_sort_from_term(h, a + 1, name);
    Z3_ast bv = sort ? term_to_ast(h, declaration_map, a) : NULL;
    return bv ? Z3_mk_fpa_to_fp_bv(ctx, bv, sort) : NULL;
  }
  if (!PL_get_arg(1, formula, a) || !PL_get_arg(2, formula, a + 1) || !PL_get_arg(3, formula, a + 2)) return NULL;
  Z3_ast rm = term_to_ast(h, declaration_map, a);
  if (rm == NULL) return NULL;
  Z3_ast x = term_to_ast(h, declaration_map, a + 1);
  if (x == NULL) return NULL;
  if (strcmp(name, "fp_to_sbv") == 0 || strcmp(name, "fp_to_ubv") == 0) {
    int width;
    if (!PL_get_integer(a + 2, &width) || width <= 0) {
      ERROR("%s: the width should be a positive integer\n", name);
      return NULL;
    }
    return name[6] == 's' ? Z3_mk_fpa_to_sbv(ctx, rm, x, (unsigned) width)
                          : Z3_mk_fpa_to_ubv(ctx, rm, x, (unsigned) width);
  }
  Z3_sort sort = fp_sort_from_term(h, a + 2, name);
  if (sort == NULL) return NULL;
  if (strcmp(name, "to_fp_unsigned") == 0) return Z3_mk_fpa_to_fp_unsigned(ctx, rm, x, sort);
  switch (Z3_get_sort_kind(ctx, Z3_get_sort(ctx, x))) {
  case Z3_INT_SORT:            return Z3_mk_fpa_to_fp_real(ctx, rm, Z3_mk_int2real(ctx, x), sort);
  case Z3_REAL_SORT:           return Z3_mk_fpa_to_fp_real(ctx, rm, x, sort);
  case Z3_FLOATING_POINT_SORT: return Z3_mk_fpa_to_fp_float(ctx, rm, x, sort);
  case Z3_BV_SORT:             return Z3_mk_fpa_to_fp_signed(ctx, rm, x, sort);
  default:
    ERROR("to_fp: cannot convert %s to floating point\n", Z3_sort_to_string(ctx, Z3_get_sort(ctx, x)));
    return NULL;
  }
}

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
    // The IEEE rounding modes, for floating-point operations: to nearest with ties to even or away
    // from zero, toward positive or negative infinity, and toward zero.
    if (strcmp(atom_string, "rne") == 0) return Z3_mk_fpa_rne(ctx);
    if (strcmp(atom_string, "rna") == 0) return Z3_mk_fpa_rna(ctx);
    if (strcmp(atom_string, "rtp") == 0) return Z3_mk_fpa_rtp(ctx);
    if (strcmp(atom_string, "rtn") == 0) return Z3_mk_fpa_rtn(ctx);
    if (strcmp(atom_string, "rtz") == 0) return Z3_mk_fpa_rtz(ctx);
    DEBUG("term_to_ast, atom %s\n", atom_string);

    Z3_ast bound = bound_variable(h, formula);
    if (bound != NULL) return bound; // shadows any declaration
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
    // By code point (Z3_mk_u32string), not Z3_mk_string, which would read \u{...} escapes in the
    // text, so backslashes and non-ASCII characters reach Z3 as they are.
    pl_wchar_t *chars;
    size_t len;
    if (!PL_get_wchars(formula, &len, &chars, CVT_STRING)) {
      ERROR("Could not convert string\n");
      return NULL;
    }
    unsigned *code_points = malloc((len > 0 ? len : 1) * sizeof(unsigned));
    if (code_points == NULL) {
      PL_resource_error("memory");
      return NULL;
    }
    for (size_t i = 0; i < len; i++) code_points[i] = (unsigned) chars[i];
    result = Z3_mk_u32string(ctx, (unsigned) len, code_points);
    free(code_points);
    return result;
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
      Z3_ast bound = bound_variable(h, name_term);
      if (bound != NULL) { // x:Sort for a variable bound by an enclosing quantifier
        if (Z3_get_sort(ctx, bound) != sort) {
          ERROR("a bound variable is used with another sort\n");
          return NULL;
        }
        return bound;
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

    if ((strcmp(name_string, "forall") == 0 || strcmp(name_string, "exists") == 0) && arity == 2) {
      return quantifier_from_term(h, declaration_map, formula, name_string[0] == 'f');
    }

    if (strcmp(name_string, "const_array") == 0) { // const_array(IndexSort, Value): Value everywhere
      CHECK_ARITY(name_string, 2, arity);
      term_t sort_term = PL_new_term_ref(), value_term = PL_new_term_ref();
      if (!PL_get_arg(1, formula, sort_term) || !PL_get_arg(2, formula, value_term)) return NULL;
      Z3_sort index_sort = mk_sort(h, sort_term);
      if (index_sort == NULL) return NULL;
      Z3_ast value = term_to_ast(h, declaration_map, value_term);
      if (value == NULL) return NULL;
      return Z3_mk_const_array(ctx, index_sort, value);
    }

    if (strcmp(name_string, "algebraic") == 0 && arity == 2) { // an algebraic number from a model
      return algebraic_from_term(h, formula);
    }

    if (strcmp(name_string, "fp_value") == 0 && arity == 2) { // fp_value(Value, Sort): a floating-point constant
      return fp_value_from_term(h, declaration_map, formula);
    }

    if (is_fp_conversion(name_string, arity)) {
      return fp_conversion_from_term(h, declaration_map, name_string, formula);
    }

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
  PRED("z3_set_timeout", 2, z3_set_timeout_foreign, 0); // +handle, +milliseconds (0: none)
  PRED("z3_reason_unknown", 2, z3_reason_unknown_foreign, 0); // +handle, -reason
  PRED("z3_interrupt", 1, z3_interrupt_foreign, 0); // +handle; from another thread
  PRED("z3_check_assumptions", 3, z3_check_assumptions_foreign, 0); // +handle, +literals, -status
  PRED("z3_get_unsat_core", 2, z3_get_unsat_core_foreign, 0); // +handle, -literals
  PRED("z3_optimize", 5, z3_optimize_foreign, 0); // +handle, +objectives, -status, -values, -model

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
  PRED("z3_finalize_memory", 0, z3_finalize_memory_foreign, 0); // raises permission_error while any handle's context exists

  PRED("handle_stats", 4, handle_stats_foreign, 0); // +handle, -A, -B, -C
  
}
