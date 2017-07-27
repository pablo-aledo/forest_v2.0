/*
 * =====================================================================================
 * /
 * |     Filename:  eight.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/10/2013 05:09:47 PM
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
	int b;
	int c;


#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
	klee_make_symbolic(&b, sizeof(b), "b");
#endif

	if(a)
		c = 1;
	else
		c = 2;

	if(b)
		c = 3;
	else
		c = 4;
	
	return 0;
}
