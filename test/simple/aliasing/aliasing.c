/*
 * =====================================================================================
 * /
 * |     Filename:  aliasing.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/16/2014 07:37:02 AM
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


int main() {
	
	int array[10] = {0,1,2,3,4,5,6,7,8,9};
	int m;
	int n;

	array[m] = 10;

	if(array[n] == 10)
		return 0;
	else
		return 1;
}
