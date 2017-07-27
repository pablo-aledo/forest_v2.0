/*
 * =====================================================================================
 * /
 * |     Filename:  random_init.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/06/2013 03:28:02 PM
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

int data[2];

int main() {
	int i, seed;


#ifdef KLEE
	klee_make_symbolic(&seed, sizeof(seed), "seed");
#endif


	seed = 0;
	for (i = 0; i < 2; i++) {
		seed = ((seed * 133) + 81) % 65535;
		data[i] = seed;
	}

	if( data[1] == 31416 )
		return 0;
	else
		return 1;
}
