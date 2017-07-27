/*
 * =====================================================================================
 * /
 * |     Filename:  force_free_hint.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/22/2014 03:40:29 PM
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


int fn(){
	int var_a = 1;
	if(var_a)
		return 1;
	else
		return 0;
}

int fn_1(){
	int a = 1;
	if(a)
		return 1;
	else 
		return 0;
}

int main() {
	fn();
	fn_1();
	return 0;
}
