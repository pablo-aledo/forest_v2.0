/*
 * =====================================================================================
 * /
 * |     Filename:  pointerincrement.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/26/2013 10:52:46 AM
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


	int variable[5];

#ifdef KLEE
	klee_make_symbolic(variable, sizeof(variable), "variable");
#endif

	int* pointer = variable;

	pointer++;

	if( *pointer == 2 )
		return 0;
	else
		return 1;
}
