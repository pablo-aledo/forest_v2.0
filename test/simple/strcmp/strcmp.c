/*
 * =====================================================================================
 * /
 * |     Filename:  strcmp.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/29/2013 12:46:09 PM
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

int strcmp(char* s1, char* s2)
{
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(unsigned char*)s1-*(unsigned char*)s2;
}

int main() {
	char str1[3];
	char str2[3];


#ifdef KLEE
	klee_make_symbolic(str1, sizeof(str1), "str1");
	klee_make_symbolic(str2, sizeof(str2), "str2");
#endif

	str1[2] = 0;
	str2[2] = 0;


	if( strcmp(str1, str2) )
		return 1;
	else
		return 0;
}
