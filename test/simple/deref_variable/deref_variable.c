/*
 * =====================================================================================
 * /
 * |     Filename:  deref_variable.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/18/2013 09:35:57 AM
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
	int array[] = {1,2,3,4,5};


#ifdef KLEE
	klee_make_symbolic(&index, sizeof(index), "index");
#endif



	if(array[index] == 3)
		return 0;
	else
		return 1;
}
