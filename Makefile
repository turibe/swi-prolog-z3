# Build and test the SWI-Prolog <-> Z3 foreign library.
#
#   make            build z3_swi_foreign.so
#   make test       build, then run the unit tests
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

.PHONY: all test clean

all: $(LIB)

$(LIB): $(SRC)
	$(SWIPL_LD) $(CFLAGS) -I$(Z3_INCLUDE) -L$(Z3_LIBDIR) -o z3_swi_foreign -shared $(SRC) -lz3

test: $(LIB)
	$(SWIPL) -g run_tests -t halt $(TEST_FILES)

clean:
	rm -f $(LIB)
