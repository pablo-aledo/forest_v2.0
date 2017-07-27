#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 

int main(void) {
	int a[5][4];

#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	if( a[2][3] == 5 ){
		return 1;	
	} else {
		return 0;
	}
}
