CSRCS     = $(wildcard *.c)
CHDRS     = $(wildcard *.h)
COBJS     = $(addsuffix .o, $(basename $(CSRCS)))

CC        = gcc
CFLAGS    = -std=c99  #-ggdb3
COPTIMIZE = -O3 -fomit-frame-pointer 

.PHONY : clean 


# To convert OBDD into reduced BDD, uncomment the following lines concerning CUDD and also uncomment the line defining REDUCTION.
# Requirement: to do this, obtain CUDD version 2.5.0 and place it in the top directory.
#CUDD_DIR  = cudd-2.5.0
#CUDD_INCLUDE = -I$(CUDD_DIR)/include
#CUDD_LIB = $(CUDD_DIR)/dddmp/libdddmp.a $(CUDD_DIR)/cudd/libcudd.a $(CUDD_DIR)/mtr/libmtr.a \
#            $(CUDD_DIR)/st/libst.a $(CUDD_DIR)/util/libutil.a $(CUDD_DIR)/epd/libepd.a


# The solver can not count a huge number of solutions beyond a cerntain threshold.
# To count precisely, install the GNU MP bignum library and uncomment the following GMPFLAGS and define GMP in MYFLAGS.
GMPFLAGS =
#GMPFLAGS += -lgmp

MYFLAGS = 
### options for formula-BDD caching ###
MYFLAGS += -D LAZY				# Cache operations are reduced (Recommended).
MYFLAGS += -D CUTSETCACHE		# cutset is selected as formula-BDD caching. If this is not defined, separator is selected.
#######################################

### options for non-blocking solver ###
MYFLAGS += -D NONBLOCKING			# non-blocking procedure is selected as a base solver. If this is not defined, blocking procedure is selected.

# select at most one of the following backtrack methods: if none of them is selected, BJ+CBJ is selected.
#MYFLAGS	+= -D BT				# Chronological backtracking
MYFLAGS	+= -D BJ				# Non-chronological backtracking with level limit
#MYFLAGS	+= -D CBJ				# Conflict-directed Back Jumping

# if DLEVEL is not defined, sublevel-based first UIP scheme is selected.
 MYFLAGS += -D DLEVEL	# decision level-based first UIP scheme

#MYFLAGS += -D REFRESH		# refresh option in command line is enabled. If the number of BDD nodes exceeds a specified threshold, all solutions are dumpted to a file (if output file is specified in command line), all caches are refreshed, and search is continued.
#######################################

#MYFLAGS += -D TRIE_REC	# Recursive version of trie implementation. If this is not defined, iterative version is used.
#MYFLAGS += -D GMP				# GNU MP bignum library is used to count solutions.
#MYFLAGS += -D REDUCTION		# Reduction of compiled OBDD into fully reduced one is performed using CUDD library (Optional).


libbddlib.a:	CFLAGS+=$(COPTIMIZE) -D NDEBUG $(MYFLAGS) 
libbddlib.a: bdd_reduce.o bddlib.o my_hash.o obdd.o solver.o trie.o
	@echo Creating library $@ 
	@rm -f $@
	ar cq $@ $^
	ranlib $@

clean:
	rm -f libbddlib.a *.o *~

## Build rule
%.o %.op %.od %.or:	%.c
	@echo Compiling: $<
	$(CC) $(CFLAGS) $(CUDD_INCLUDE) -c -o $@ $<

