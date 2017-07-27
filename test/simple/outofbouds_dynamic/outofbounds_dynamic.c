/*
 * =====================================================================================
 * /
 * |     Filename:  outofbounds_dynamic.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/02/2015 10:54:14 AM
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
	if(b > 5) return 0;
	if(a[b])
		return 0;
	else
		return 1;
}
