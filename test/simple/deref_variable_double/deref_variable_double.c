/*
 * =====================================================================================
 * /
 * |     Filename:  deref_variable_double.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  02/27/2014 05:06:32 AM
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


int a[5] = {6,7,8,9,0};
int b[3] = {5,6,7};
int* c[2];

int main() {

	c[0] = a;
	c[1] = b;

	int index = 0;

	int d = *(c[index]);

	if(d == 5)
		return 0;
	else
		return 1;
}
