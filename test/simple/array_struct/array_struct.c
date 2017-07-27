/*
 * =====================================================================================
 * /
 * |     Filename:  struct.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  30/07/2013 12:58:56 AM
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


struct Estructura3 {
	int entero4;
	int entero5;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura3 estructura3;
};

int main(){

	struct Estructura a[10];

#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	if( a[5].entero1 > 0 )
		return 0;
	else
		return 1;
}
