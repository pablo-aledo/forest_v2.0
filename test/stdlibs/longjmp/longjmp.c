/*
 * =====================================================================================
 * /
 * |     Filename:  longjmp.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/08/2014 09:45:28 AM
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

#include <setjmp.h>

jmp_buf env;

void function(){
	longjmp(env,1);
}

int main() {

	if(setjmp(env)){
		return 1;
	} else {
		function();
	}

	return 0;
}
