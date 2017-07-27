/*
 * =====================================================================================
 * /
 * |     Filename:  globals_always_free.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/15/2014 12:00:45 PM
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

int a;

int main() {

	a = 1 - a;
	
	if( a == 5 )
		return 0;
	else
		return 1;

}
