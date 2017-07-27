/*
 * =====================================================================================
 * /
 * |     Filename:  array_function_pointers.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/28/2015 02:35:32 PM
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

int func_0(){ return 0; }
int func_1(){ return 1; }
int func_2(){ return 2; }

int main() {
	
	int (*array_of_functions[3])();
	int n;

	array_of_functions[0] = func_0;
	array_of_functions[1] = func_1;
	array_of_functions[2] = func_2;

	if(array_of_functions[n]() == 1) return 1;
	else return 0;
}
