/*
 * =====================================================================================
 * /
 * |     Filename:  verifier_assert.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/09/2014 09:48:22 AM
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

void __VERIFIER_assert(int);

int main() {
	int i;
	__VERIFIER_assert(i != 0);
	return 0;
}
