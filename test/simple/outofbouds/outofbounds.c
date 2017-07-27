/*
 * =====================================================================================
 * /
 * |     Filename:  outofbounds.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/29/2013 04:54:45 PM
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

	int a[5];
	int b;
	if(a[5])
		return 0;
	else
		return 1;
}
