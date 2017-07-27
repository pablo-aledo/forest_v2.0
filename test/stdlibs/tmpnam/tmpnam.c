/*
 * =====================================================================================
 * /
 * |     Filename:  tmpnam.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/09/2014 12:02:02 PM
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

#include <stdio.h>

int main() {
	
	char a[20];
	tmpnam(a);
	printf("%s\n", a);
	/*if( a[1] == '0' )*/
		return 0;
	/*else */
		/*return 1;*/
}
