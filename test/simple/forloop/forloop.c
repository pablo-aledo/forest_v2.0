/*
 * =====================================================================================
 * /
 * |     Filename:  forloop.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/24/2013 10:22:45 AM
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



int main() {
	int a;
	
#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
#endif

	unsigned int i;

	for ( i = 0; i < 10; i++) {
		if( i == a ) return 0;
	}
	return 0;
}
