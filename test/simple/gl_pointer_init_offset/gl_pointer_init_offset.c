/*
 * =====================================================================================
 * /
 * |     Filename:  gl_pointer_init_offset.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/15/2013 10:10:36 AM
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

int x;
char a[10];
char* b = a + 1;

int main() {


#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	if(*b)
		return 0;
	else
		return 1;
}
