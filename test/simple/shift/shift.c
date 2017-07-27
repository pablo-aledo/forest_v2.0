/*
 * =====================================================================================
 * /
 * |     Filename:  shift.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/15/2013 06:35:32 PM
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

	if(a >> 2 == 10) return 0;
	else return 1;
}
