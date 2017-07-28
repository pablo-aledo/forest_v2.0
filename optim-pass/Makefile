#all: /llvm-2.9/install/lib/ForestInstr.so /llvm-2.9/install/lib/ForestConcurrency.so /llvm-2.9/install/lib/ForestStdlibs.so /llvm-2.9/install/lib/ForestHeuristic.so /llvm-2.9/install/lib/ForestBcAnalyze.so /llvm-2.9/install/lib/ForestFeatures.so
all: /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestInstr.so

/usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestInstr.so: instrumentation_pass.cpp 
	mkdir -p /usr/src/llvm-3.7/build3/lib/Transforms/Forest_instr/
	mkdir -p /usr/src/llvm-3.7/lib/Transforms/Forest_instr/
	\cp make_instr /usr/src/llvm-3.7/build3/lib/Transforms/Forest_instr/Makefile
	\cp make_instr /usr/src/llvm-3.7/lib/Transforms/Forest_instr/Makefile
	\cp instrumentation_pass.cpp /usr/src/llvm-3.7/lib/Transforms/Forest_instr/forest_instr.cpp 
	cd /usr/src/llvm-3.7/build3/lib/Transforms/Forest_instr/; make
	cd /usr/src/llvm-3.7/build3/lib/Transforms/Forest_instr/; sudo make install;

#/llvm-2.9/install/lib/ForestConcurrency.so: concurrency_pass.cpp
	#mkdir -p /llvm-2.9/lib/Transforms/Forest_concurrency/
	#cp make_concurrency /llvm-2.9/lib/Transforms/Forest_concurrency/Makefile
	#cp concurrency_pass.cpp /llvm-2.9/lib/Transforms/Forest_concurrency/Forest_concurrency.cpp 
	#cd /llvm-2.9/lib/Transforms/Forest_concurrency/; make;
	#cd /llvm-2.9/lib/Transforms/Forest_concurrency/; make install;

#/llvm-2.9/install/lib/ForestStdlibs.so: stdlibs_pass.cpp
	#mkdir -p /llvm-2.9/lib/Transforms/Forest_stdlibs/
	#cp make_stdlibs /llvm-2.9/lib/Transforms/Forest_stdlibs/Makefile
	#cp stdlibs_pass.cpp /llvm-2.9/lib/Transforms/Forest_stdlibs/Forest_stdlibs.cpp 
	#cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; make;
	#cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; make install;

#/llvm-2.9/install/lib/ForestHeuristic.so: heuristic_pass.cpp
	#mkdir -p /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp make_heuristic /llvm-2.9/lib/Transforms/Forest_heuristic/Makefile
	#cp heuristic_pass.cpp                 /llvm-2.9/lib/Transforms/Forest_heuristic/Forest_heuristic.cpp 
	#cp graph/DijkstraShortestPathAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/DijkstraShortestPathAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/Graph.cpp                    /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/Graph.h                      /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/GraphElements.h              /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/YenTopKShortestPathsAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cp graph/YenTopKShortestPathsAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	#cd /llvm-2.9/lib/Transforms/Forest_heuristic/; make;
	#cd /llvm-2.9/lib/Transforms/Forest_heuristic/; make install;

#/llvm-2.9/install/lib/ForestBcAnalyze.so: bc_analyze.cpp
	#mkdir -p /llvm-2.9/lib/Transforms/Forest_bc_analyze/
	#cp make_bc_analyze /llvm-2.9/lib/Transforms/Forest_bc_analyze/Makefile
	#cp bc_analyze.cpp /llvm-2.9/lib/Transforms/Forest_bc_analyze/Forest_bc_analyze.cpp 
	#cd /llvm-2.9/lib/Transforms/Forest_bc_analyze/; make;
	#cd /llvm-2.9/lib/Transforms/Forest_bc_analyze/; make install;

#/llvm-2.9/install/lib/ForestFeatures.so: features.cpp
	#mkdir -p /llvm-2.9/lib/Transforms/Forest_Features/
	#cp make_features /llvm-2.9/lib/Transforms/Forest_Features/Makefile
	#cp features.cpp /llvm-2.9/lib/Transforms/Forest_Features/Forest_Features.cpp 
	#cd /llvm-2.9/lib/Transforms/Forest_Features/; make;
	#cd /llvm-2.9/lib/Transforms/Forest_Features/; make install;

clean:
	rm -rf /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestInstr.so
	rm -rf /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestConcurrency.so
	rm -rf /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestStdlibs.so
	rm -rf /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestBcAnalyze.so
	rm -rf /llvm-2.9/lib/Transforms/Forest_instr/
	rm -rf /llvm-2.9/lib/Transforms/Forest_concurrency/
	rm -rf /llvm-2.9/lib/Transforms/Forest_stdlibs/
	rm -rf /llvm-2.9/lib/Transforms/Forest_heuristic/
	rm -rf /llvm-2.9/lib/Transforms/Forest_bc_analyze/
