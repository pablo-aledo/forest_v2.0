/*
 * =====================================================================================
 * /
 * |     Filename:  deref_variable_store.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/22/2014 06:59:24 PM
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
	int index = 0;
	int array[] = {0,0,0,0,0,0};


#ifdef KLEE
	klee_make_symbolic(&index, sizeof(index), "index");
#endif


	array[index] = 5;

	if(array[3] == 5)
		return 0;
	else
		return 1;
}

