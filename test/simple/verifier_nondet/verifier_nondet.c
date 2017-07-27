/*
 * =====================================================================================
 * /
 * |     Filename:  verifier_nondet.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/08/2014 02:38:55 PM
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


int __VERIFIER_nondet_int();

int main() {
	int a = __VERIFIER_nondet_int();
	if(a)
		return 0;
	else
		return 1;
}
