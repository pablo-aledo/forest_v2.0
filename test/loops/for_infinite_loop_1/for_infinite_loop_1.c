
#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 

int main() {

	int x;

	for(;;) {
		if(x > 0) return 1;
	}

}

