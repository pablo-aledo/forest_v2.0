/*
 * =====================================================================================
 * /
 * |     Filename:  verifier_assume.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/09/2014 05:05:02 AM
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

void __VERIFIER_assume(int);

int main() {
	int i;
	__VERIFIER_assume(i > 0);

	if(i == -1) return 0;
	else if(i == 1) return 1;
	else return 2;
}
