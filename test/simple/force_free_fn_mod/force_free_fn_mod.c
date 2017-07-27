/*
 * =====================================================================================
 * /
 * |     Filename:  force_free_fn_mod.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/19/2014 04:18:52 PM
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

void force_free(int* a);

int main() {
	
	int a = 5; force_free(&a);

	a = 1-a;

	if(a == 5)
		return 0;
	else 
		return 1;
}
