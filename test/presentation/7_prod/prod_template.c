/*
 * =====================================================================================
 * /
 * |     Filename:  prod.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/27/2013 09:31:28 AM
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

#define N %n%

int main() {

	int a[N];
	int prod = 1;

#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	for ( unsigned int i = 0; i < N; i++) {
		prod *= a[i];
	}

	if(prod == 1000)
		return 0;
	else
		return 1;
}
