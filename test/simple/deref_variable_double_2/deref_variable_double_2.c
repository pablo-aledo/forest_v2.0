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


int a[10] = {0,1,2,3,4,5,6,7,8,9};
int* b[2];

int main() {

	int index_1 = 0;
	int index_2 = 0;

	b[0] = a;
	b[1] = a+index_1;

	int c = *(b[index_2]);

	if(c == 5)
		return 0;
	else
		return 1;
}
