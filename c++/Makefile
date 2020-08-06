CXXFLAGS = -std=c++17 -O3 #-ggdb3 
CPPFLAGS = -DNDEBUG 
ADDFLAGS =

.PHONY: all clean picosat bddlib

all: convex convex_dfs convex_dfs_parallel

convex: dpll.hpp common.hpp convex.cpp
	g++ $(CXXFLAGS) $(CPPFLAGS) -D_USE_SHARED_PTR $(ADDFLAGS) -o convex convex.cpp

convex_dfs: dpll.hpp common.hpp convex_dfs.cpp
	g++ $(CXXFLAGS) $(CPPFLAGS) $(ADDFLAGS) -o convex_dfs convex_dfs.cpp

convex_dfs_parallel: dpll.hpp common.hpp convex_dfs.cpp
	g++ $(CXXFLAGS) $(CPPFLAGS) -D_PARALLEL $(ADDFLAGS) -o convex_dfs_parallel convex_dfs.cpp  -ltbb

bdd_convex: bddsolver.hpp common.hpp convex.cpp bddlib/libbddlib.a
	g++ $(CXXFLAGS) $(CPPFLAGS) -D_USE_SHARED_PTR -DBDD_CONVEX $(ADDFLAGS) -o bdd_convex convex.cpp -L bddlib -lbddlib

pico_convex: picosolver.hpp common.hpp convex.cpp 
	g++ $(CXXFLAGS) $(CPPFLAGS) -D_USE_SHARED_PTR -DPICO_CONVEX $(ADDFLAGS) -o pico_convex convex.cpp -L picosat -lpicosat

test_dpll: dpll.hpp test_dpll.cpp
	g++ $(CXXFLAGS) $(CPPFLAGS) $(ADDFLAGS) -o test_dpll test_dpll.cpp

test_bdd: subdirs test_bdd.cpp bddsolver.hpp bddlib/bddlib.a
	g++ $(CXXFLAGS) $(CPPFLAGS) $(ADDFLAGS) -o test_bdd test_bdd.cpp bddlib/bddlib.a

bddlib:
	make -C bddlib/

picosat:
	make -C picosat/

clean:
	rm -f *~
	rm -f convex
	rm -f convex_dfs
	rm -f convex_dfs_parallel
	rm -f bdd_convex
	rm -f pico_convex
	rm -f test_dpll
	rm -f test_bdd
	make -C bddlib/ clean
	make -C picosat/ clean
