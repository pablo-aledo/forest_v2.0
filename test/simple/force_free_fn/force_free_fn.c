/*
 * =====================================================================================
 * /
 * |     Filename:  force_free_fn.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/06/2013 03:06:42 AM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */


#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 




void force_free(int* a);

int main() {
	
	int a = 5;

#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
#else
	force_free(&a);
#endif
	if(a == 5)
		return 0;
	else
		return 1;
}
