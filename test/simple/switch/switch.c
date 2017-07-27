/*
 * =====================================================================================
 * /
 * |     Filename:  switch.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/20/2013 04:39:48 PM
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

	switch(a){
		case 1: return 0;
		case 2: return 1;
		case 3: case 4: return 2;
	}
	return 0;
}
