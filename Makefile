# Build and test the SWI-Prolog <-> Z3 foreign library.
#
#   make            build z3_swi_foreign.so
#   make test       build, then run the unit tests
#   make einstein   build, then solve the Einstein puzzle in examples/einstein.pl
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

# macOS: a Z3 built from source gives libz3.dylib the bare install name "libz3.dylib", which the
# linker copies into $(LIB), so macOS then looks for libz3.dylib in the current directory and the
# library only loads from this one. After linking, point that reference at Z3_LIBDIR instead:
# @loader_path (the directory holding $(LIB)) for the default ".", or an absolute path otherwise.
# A Z3 with an absolute install name, such as Homebrew's, is left as it is.
ifeq ($(shell uname -s),Darwin)
  ifeq ($(Z3_LIBDIR),.)
    Z3_DYLIB_PATH = @loader_path/libz3.dylib
  else
    Z3_DYLIB_PATH = $(abspath $(Z3_LIBDIR))/libz3.dylib
  endif
  FIX_Z3_PATH = install_name_tool -change libz3.dylib $(Z3_DYLIB_PATH) $(LIB)
else
  FIX_Z3_PATH = true
endif

.PHONY: all test einstein clean

all: $(LIB)

$(LIB): $(SRC)
	$(SWIPL_LD) $(CFLAGS) -I$(Z3_INCLUDE) -L$(Z3_LIBDIR) -o z3_swi_foreign -shared $(SRC) -lz3
	$(FIX_Z3_PATH)

test: $(LIB)
	$(SWIPL) -g run_tests -t halt $(TEST_FILES)

einstein: $(LIB)
	$(SWIPL) -q examples/einstein.pl

clean:
	rm -f $(LIB)
