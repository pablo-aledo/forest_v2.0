LLVM_SRC_HOME=/usr/src/llvm-3.7
all: ${LLVM_SRC_HOME}/build/Debug+Asserts/lib/ForestInstr.so

${LLVM_SRC_HOME}/build/Debug+Asserts/lib/ForestInstr.so: instrumentation_pass.cpp 
	mkdir -p ${LLVM_SRC_HOME}/build/lib/Transforms/Forest_instr/
	mkdir -p ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/
	\cp make_instr ${LLVM_SRC_HOME}/build/lib/Transforms/Forest_instr/Makefile
	\cp make_instr ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/Makefile
	\cp instrumentation_pass.cpp ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/forest_instr.cpp 
	\cp ../back-end/architecture.cpp ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/architecture.cpp 
	\cp ../back-end/architecture.h ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/architecture.h
	\cp ../back-end/utils.h ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/utils.h
	\cp ../back-end/utils.cpp ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/utils.cpp 
	\cp ../back-end/options.h ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/options.h
	\cp ../back-end/options.cpp ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/options.cpp
	cd ${LLVM_SRC_HOME}/build/lib/Transforms/Forest_instr/; make
	cd ${LLVM_SRC_HOME}/build/lib/Transforms/Forest_instr/; sudo make install;

clean:
	rm -rf /usr/src/llvm-3.7/build/Debug+Asserts/lib/ForestInstr.so
