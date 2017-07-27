/*
 * =====================================================================================
 * /
 * |     Filename:  function_pointer.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/28/2015 11:12:10 AM
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

int func(){
	return 5;
}

int main() {
	
	int (*func_pointer)() = func;

	if(func_pointer()) return 0;
	else return 1;
}
