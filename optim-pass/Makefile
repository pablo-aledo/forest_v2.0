all: /llvm-2.9/install/lib/ForestInstr.so /llvm-2.9/install/lib/ForestMeasure.so /llvm-2.9/install/lib/ForestConcurrency.so /llvm-2.9/install/lib/ForestStdlibs.so /llvm-2.9/install/lib/ForestHeuristic.so /llvm-2.9/install/lib/ForestBcAnalyze.so /llvm-2.9/install/lib/ForestFeatures.so

/llvm-2.9/install/lib/ForestInstr.so: instrumentation_pass.cpp 
	mkdir -p /llvm-2.9/lib/Transforms/Forest_instr/
	cp make_instr /llvm-2.9/lib/Transforms/Forest_instr/Makefile
	cp instrumentation_pass.cpp /llvm-2.9/lib/Transforms/Forest_instr/forest_instr.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_instr/; make;
	cd /llvm-2.9/lib/Transforms/Forest_instr/; make install;

/llvm-2.9/install/lib/ForestMeasure.so: measurement_pass.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_measure/
	cp make_measure /llvm-2.9/lib/Transforms/Forest_measure/Makefile
	cp measurement_pass.cpp /llvm-2.9/lib/Transforms/Forest_measure/Forest_measure.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_measure/; make;
	cd /llvm-2.9/lib/Transforms/Forest_measure/; make install;

/llvm-2.9/install/lib/ForestConcurrency.so: concurrency_pass.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_concurrency/
	cp make_concurrency /llvm-2.9/lib/Transforms/Forest_concurrency/Makefile
	cp concurrency_pass.cpp /llvm-2.9/lib/Transforms/Forest_concurrency/Forest_concurrency.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_concurrency/; make;
	cd /llvm-2.9/lib/Transforms/Forest_concurrency/; make install;

/llvm-2.9/install/lib/ForestStdlibs.so: stdlibs_pass.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_stdlibs/
	cp make_stdlibs /llvm-2.9/lib/Transforms/Forest_stdlibs/Makefile
	cp stdlibs_pass.cpp /llvm-2.9/lib/Transforms/Forest_stdlibs/Forest_stdlibs.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; make;
	cd /llvm-2.9/lib/Transforms/Forest_stdlibs/; make install;

/llvm-2.9/install/lib/ForestHeuristic.so: heuristic_pass.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp make_heuristic /llvm-2.9/lib/Transforms/Forest_heuristic/Makefile
	cp heuristic_pass.cpp                 /llvm-2.9/lib/Transforms/Forest_heuristic/Forest_heuristic.cpp 
	cp graph/DijkstraShortestPathAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/DijkstraShortestPathAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/Graph.cpp                    /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/Graph.h                      /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/GraphElements.h              /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/YenTopKShortestPathsAlg.cpp  /llvm-2.9/lib/Transforms/Forest_heuristic/
	cp graph/YenTopKShortestPathsAlg.h    /llvm-2.9/lib/Transforms/Forest_heuristic/
	cd /llvm-2.9/lib/Transforms/Forest_heuristic/; make;
	cd /llvm-2.9/lib/Transforms/Forest_heuristic/; make install;

/llvm-2.9/install/lib/ForestBcAnalyze.so: bc_analyze.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_bc_analyze/
	cp make_bc_analyze /llvm-2.9/lib/Transforms/Forest_bc_analyze/Makefile
	cp bc_analyze.cpp /llvm-2.9/lib/Transforms/Forest_bc_analyze/Forest_bc_analyze.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_bc_analyze/; make;
	cd /llvm-2.9/lib/Transforms/Forest_bc_analyze/; make install;

/llvm-2.9/install/lib/ForestFeatures.so: features.cpp
	mkdir -p /llvm-2.9/lib/Transforms/Forest_Features/
	cp make_features /llvm-2.9/lib/Transforms/Forest_Features/Makefile
	cp features.cpp /llvm-2.9/lib/Transforms/Forest_Features/Forest_Features.cpp 
	cd /llvm-2.9/lib/Transforms/Forest_Features/; make;
	cd /llvm-2.9/lib/Transforms/Forest_Features/; make install;

clean:
	rm -rf /llvm-2.9/install/lib/ForestInstr.so
	rm -rf /llvm-2.9/install/lib/ForestMeasure.so
	rm -rf /llvm-2.9/install/lib/ForestConcurrency.so
	rm -rf /llvm-2.9/install/lib/ForestStdlibs.so
	rm -rf /llvm-2.9/install/lib/ForestBcAnalyze.so
	rm -rf /llvm-2.9/lib/Transforms/Forest_instr/
	rm -rf /llvm-2.9/lib/Transforms/Forest_measure/
	rm -rf /llvm-2.9/lib/Transforms/Forest_concurrency/
	rm -rf /llvm-2.9/lib/Transforms/Forest_stdlibs/
	rm -rf /llvm-2.9/lib/Transforms/Forest_heuristic/
	rm -rf /llvm-2.9/lib/Transforms/Forest_bc_analyze/
