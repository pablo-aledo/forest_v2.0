/*
 * =====================================================================================
 * /
 * |     Filename:  charnull.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/13/2013 01:51:45 PM
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

char* program_name;

int main()
{

#ifdef KLEE
	klee_make_symbolic(&program_name, sizeof(program_name), "program_name");
#endif

	if(program_name)
		return 1;
	else
		return 0;
}
