/*
 * =====================================================================================
 * /
 * |     Filename:  array_struct_global.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/30/2013 03:10:29 PM
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

struct Estructura a[10];

int main(){

#ifdef KLEE
	klee_make_symbolic(a, sizeof(a), "a");
#endif

	if( a[5].estructura3.entero5 > 0 )
		return 0;
	else
		return 1;
}
