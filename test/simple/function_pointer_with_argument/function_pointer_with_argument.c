/*
 * =====================================================================================
 * /
 * |     Filename:  function_pointer_with_argument.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/01/2015 04:10:17 PM
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

int func(int a){
	return 5;
}

int main() {
	
	int (*func_pointer)(int) = func;

	if(func_pointer(2)) return 0;
	else return 1;
}
