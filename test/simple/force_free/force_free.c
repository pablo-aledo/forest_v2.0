/*
 * =====================================================================================
 * /
 * |     Filename:  force_free.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/06/2013 08:57:02 AM
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

int a = 5;

int main() {

#ifdef KLEE
	klee_make_symbolic(&a, sizeof(a), "a");
#endif
	
	if( a == 5 )
		return 0;
	else
		return 1;

}
