/*
 * =====================================================================================
 * /
 * |     Filename:  fnarray.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/08/2013 04:51:55 PM
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

/*#include <stdio.h>*/


#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 


#define SIZE 2

int c[SIZE+1][SIZE+1];// = {0,4,8,12,16,20,24,28,32};

int elem11(int c_param[SIZE+1][SIZE+1]) {

	return c_param[1][1];

}

int main() {

#ifdef KLEE
	klee_make_symbolic(c, sizeof(c), "c");
#endif


	/*printf("%d\n", elem11(c));*/
	if( elem11(c) == 0 )
		return 0;
	else
		return 1;
}
	 

