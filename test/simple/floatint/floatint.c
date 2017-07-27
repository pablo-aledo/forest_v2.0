/*
 * =====================================================================================
 * /
 * |     Filename:  float.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/01/2013 07:36:59 PM
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



int main(){

	int a;
	float b;

#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
	klee_make_symbolic(&b, sizeof(b), "b");
#endif

	if( a*b == 5 )
		return 0;
	else
		return 1;

}
