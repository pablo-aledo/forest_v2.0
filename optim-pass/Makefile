LLVM_SRC_HOME=/usr/src/llvm-3.7
all: ${LLVM_SRC_HOME}/build3/Debug+Asserts/lib/ForestInstr.so

${LLVM_SRC_HOME}/build3/Debug+Asserts/lib/ForestInstr.so: instrumentation_pass.cpp 
	mkdir -p ${LLVM_SRC_HOME}/build3/lib/Transforms/Forest_instr/
	mkdir -p ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/
	\cp make_instr ${LLVM_SRC_HOME}/build3/lib/Transforms/Forest_instr/Makefile
	\cp make_instr ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/Makefile
	\cp instrumentation_pass.cpp ${LLVM_SRC_HOME}/lib/Transforms/Forest_instr/forest_instr.cpp 
	cd ${LLVM_SRC_HOME}/build3/lib/Transforms/Forest_instr/; make
	cd ${LLVM_SRC_HOME}/build3/lib/Transforms/Forest_instr/; sudo make install;

clean:
	rm -rf /usr/src/llvm-3.7/build3/Debug+Asserts/lib/ForestInstr.so
