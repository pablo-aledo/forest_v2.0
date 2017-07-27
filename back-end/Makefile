CCXX=g++
CC=gcc

all: ../lib/forest.a 

../lib/forest.a: ../build/database.o ../build/operators.o ../build/solver_wrapper.o ../build/all_solvers.o ../build/z3_variable.o ../build/linear_variable.o ../build/poly_variable.o ../build/variable.o ../build/z3_solver.o ../build/linear_solver.o ../build/interpolant_solver.o ../build/mixed_int.o ../build/mixed_bblast.o ../build/linear_bblast.o ../build/linear_variable_bb.o ../build/polynomic_solver.o ../build/z3_bitvector.o ../build/z3_realint.o ../build/sqlite.o ../build/utils.o ../build/options.o ../build/wrapper.o ../build/measurement.o ../build/timer.o ../build/architecture.o ../build/assignment.o ../build/state.o ../build/automaton.o ../build/uppaal.o ../build/concurrency_backend.o ../build/memory_allocator.o ../build/pre_post.o
	ar rcs ../lib/forest.a ../build/database.o ../build/operators.o ../build/solver_wrapper.o ../build/all_solvers.o ../build/z3_variable.o ../build/linear_variable.o ../build/poly_variable.o ../build/variable.o ../build/z3_solver.o ../build/linear_solver.o ../build/interpolant_solver.o ../build/mixed_int.o ../build/mixed_bblast.o ../build/linear_bblast.o ../build/linear_variable_bb.o ../build/linear_bblast.o ../build/polynomic_solver.o ../build/z3_bitvector.o ../build/z3_realint.o ../build/sqlite.o ../build/utils.o ../build/options.o ../build/wrapper.o ../build/measurement.o ../build/timer.o ../build/architecture.o ../build/assignment.o ../build/state.o ../build/automaton.o ../build/uppaal.o ../build/concurrency_backend.o ../build/memory_allocator.o ../build/pre_post.o
	#llvm-link -o=../lib/forest.a ../build/database.o ../build/operators.o ../build/solver_wrapper.o ../build/all_solvers.o ../build/z3_variable.o ../build/linear_variable.o ../build/poly_variable.o ../build/variable.o ../build/z3_solver.o ../build/linear_solver.o ../build/mixed_int.o ../build/mixed_bblast.o ../build/linear_bblast.o ../build/linear_variable_bb.o ../build/polynomic_solver.o ../build/z3_bitvector.o ../build/z3_realint.o ../build/sqlite.o ../build/utils.o ../build/options.o ../build/wrapper.o ../build/measurement.o ../build/timer.o ../build/architecture.o

../build/wrapper.o: wrapper.cpp
	$(CCXX) -g -c wrapper.cpp -o ../build/wrapper.o

../build/options.o: options.cpp
	$(CCXX) -g -c options.cpp -o ../build/options.o

../build/utils.o: utils.cpp 
	$(CCXX) -g -c utils.cpp -o ../build/utils.o

../build/database.o: database.cpp
	$(CCXX) -g -c database.cpp -o ../build/database.o

../build/operators.o: operators.cpp
	$(CCXX) -g -c operators.cpp -o ../build/operators.o

../build/solver_wrapper.o: solver_wrapper.cpp
	$(CCXX) -g -c solver_wrapper.cpp -o ../build/solver_wrapper.o

../build/all_solvers.o: all_solvers.cpp
	$(CCXX) -g -c all_solvers.cpp -o ../build/all_solvers.o

../build/linear_variable.o: linear_variable.cpp
	$(CCXX) -g -c linear_variable.cpp -o ../build/linear_variable.o

../build/poly_variable.o: poly_variable.cpp
	$(CCXX) -g -c poly_variable.cpp -o ../build/poly_variable.o

../build/z3_variable.o: z3_variable.cpp
	$(CCXX) -g -c z3_variable.cpp -o ../build/z3_variable.o

../build/variable.o: variable.cpp
	$(CCXX) -g -c variable.cpp -o ../build/variable.o

../build/z3_solver.o: z3_solver.cpp
	$(CCXX) -g -c z3_solver.cpp -o ../build/z3_solver.o

../build/linear_solver.o: linear_solver.cpp
	$(CCXX) -g -c linear_solver.cpp -o ../build/linear_solver.o

../build/interpolant_solver.o: interpolant_solver.cpp
	$(CCXX) -g -c interpolant_solver.cpp -o ../build/interpolant_solver.o

../build/mixed_int.o: mixed_int.cpp
	$(CCXX) -g -c mixed_int.cpp -o ../build/mixed_int.o

../build/mixed_bblast.o: mixed_bblast.cpp
	$(CCXX) -g -c mixed_bblast.cpp -o ../build/mixed_bblast.o

../build/linear_bblast.o: linear_bblast.cpp
	$(CCXX) -g -c linear_bblast.cpp -o ../build/linear_bblast.o


../build/linear_variable_bb.o: linear_variable_bb.cpp
	$(CCXX) -g -c linear_variable_bb.cpp -o ../build/linear_variable_bb.o


../build/polynomic_solver.o: polynomic_solver.cpp
	$(CCXX) -g -c polynomic_solver.cpp -o ../build/polynomic_solver.o

../build/z3_bitvector.o: z3_bitvector.cpp
	$(CCXX) -g -c z3_bitvector.cpp -o ../build/z3_bitvector.o

../build/z3_realint.o: z3_realint.cpp
	$(CCXX) -g -c z3_realint.cpp -o ../build/z3_realint.o

../build/sqlite.o: sqlite3.c
	$(CC) -g -c sqlite3.c -o ../build/sqlite.o

../build/measurement.o: measurement.cpp 
	$(CCXX) -g -c measurement.cpp -o ../build/measurement.o

../build/timer.o: timer.cpp 
	$(CCXX) -g -c timer.cpp -o ../build/timer.o 

../build/architecture.o: architecture.cpp 
	$(CCXX) -g -c architecture.cpp -o ../build/architecture.o 

../build/assignment.o: assignment.cpp 
	$(CCXX) -g -c assignment.cpp -o ../build/assignment.o 

../build/state.o: state.cpp 
	$(CCXX) -g -c state.cpp -o ../build/state.o 

../build/automaton.o: automaton.cpp 
	$(CCXX) -g -c automaton.cpp -o ../build/automaton.o 

../build/uppaal.o: uppaal.cpp 
	$(CCXX) -g -c uppaal.cpp -o ../build/uppaal.o 

../build/concurrency_backend.o: concurrency_backend.cpp 
	$(CCXX) -g -c concurrency_backend.cpp -o ../build/concurrency_backend.o 

../build/memory_allocator.o: memory_allocator.cpp 
	$(CCXX) -g -c memory_allocator.cpp -o ../build/memory_allocator.o 

../build/pre_post.o: pre_post.cpp 
	$(CCXX) -g -c pre_post.cpp -o ../build/pre_post.o 


