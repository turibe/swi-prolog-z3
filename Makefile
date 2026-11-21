# Build and test the SWI-Prolog <-> Z3 foreign library.
#
#   make            build z3_swi_foreign.so
#   make test       build, then run the unit tests
#   make einstein   build, then solve the Einstein puzzle in examples/einstein.pl
#   make leaks      build, then check the C code for memory leaks (macOS only; see test/leaks.pl)
#   make clean      remove the built library
#
# Point the build at your Z3 install by overriding these, for example:
#   make Z3_INCLUDE=/opt/homebrew/include Z3_LIBDIR=/opt/homebrew/lib
#
# Z3_LIBDIR defaults to this directory, which should hold a link to (or copy of) libz3.dylib.

Z3_INCLUDE ?= $(HOME)/git/z3/src/api
Z3_LIBDIR  ?= .

SWIPL    ?= swipl
SWIPL_LD ?= swipl-ld
CFLAGS   ?= -O3 -Wall

LIB        = z3_swi_foreign.so
SRC        = z3_swi_foreign.c
TEST_FILES = z3.pl stateful_repl.pl z3_swi_foreign.pl

# macOS: the linker copies libz3.dylib's install name into $(LIB), and that name decides where
# macOS looks for libz3 at load time. Z3 builds differ:
#   - Z3's Python build (mk_make.py): the bare name "libz3.dylib", found only in the current directory;
#   - Z3's CMake build: "@rpath/libz3.<version>.dylib", not found at all, since $(LIB) has no rpath;
#   - Homebrew: an absolute path, which works as it is.
# So after linking, a reference that is not an absolute path is pointed at Z3_LIBDIR instead:
# @loader_path (the directory holding $(LIB)) for the default ".", or an absolute path otherwise.
# Linking with -headerpad_max_install_names leaves room for the new, possibly longer, name.
ifeq ($(shell uname -s),Darwin)
  ifeq ($(Z3_LIBDIR),.)
    Z3_DYLIB_PATH = @loader_path/libz3.dylib
  else
    Z3_DYLIB_PATH = $(abspath $(Z3_LIBDIR))/libz3.dylib
  endif
  LDFLAGS += -Wl,-headerpad_max_install_names
  FIX_Z3_PATH = ref=$$(otool -L $(LIB) | awk 'NR > 1 && /libz3/ { print $$1; exit }'); \
    case "$$ref" in \
      "") echo "warning: no libz3 reference found in $(LIB)" ;; \
      /*) ;; \
      *) echo "install_name_tool -change $$ref $(Z3_DYLIB_PATH) $(LIB)"; \
         install_name_tool -change "$$ref" $(Z3_DYLIB_PATH) $(LIB) ;; \
    esac
else
  FIX_Z3_PATH = true
endif

.PHONY: all test einstein leaks clean

all: $(LIB)

$(LIB): $(SRC)
	$(SWIPL_LD) $(CFLAGS) $(LDFLAGS) -I$(Z3_INCLUDE) -L$(Z3_LIBDIR) -o z3_swi_foreign -shared $(SRC) -lz3
	@$(FIX_Z3_PATH)

test: $(LIB)
	$(SWIPL) -g run_tests -t halt $(TEST_FILES)

einstein: $(LIB)
	$(SWIPL) -q examples/einstein.pl

# Runs a workload under macOS's leaks tool and fails if any leaked block was allocated with
# z3_swi_foreign.so on its call stack. The workload's expected error messages go to LEAKS_LOG.
LEAK_ITERATIONS ?= 2000
LEAKS_LOG       ?= $(or $(TMPDIR),/tmp/)z3-leaks-stderr.log

leaks: $(LIB)
	@if [ "$$(uname -s)" != Darwin ]; then echo "make leaks needs macOS's leaks tool"; exit 1; fi
	@MallocStackLogging=1 $(SWIPL) -q test/leaks.pl $(LEAK_ITERATIONS) 2>"$(LEAKS_LOG)" \
	  || { echo "(messages from the workload are in $(LEAKS_LOG))"; exit 1; }

clean:
	rm -f $(LIB)
