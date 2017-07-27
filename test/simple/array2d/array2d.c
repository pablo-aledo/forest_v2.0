#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 

int a[2][2] = { {1,2}, {3,4} };
/*int a[2][2];*/

int main(void) {


#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	if( a[1][1] == 5 ){
		return 1;	
	} else {
		return 0;
	}
}
