/*
 * =====================================================================================
 * /
 * |     Filename:  division.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/05/2013 11:20:09 AM
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
	int a = 1;
	int b = 1;


#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
	klee_make_symbolic(&b, sizeof(b), "b");
#endif


	if(a/b == 4)
		return 0;
	else 
		return 1;
}
