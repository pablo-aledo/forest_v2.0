/*
 * =====================================================================================
 * /
 * |     Filename:  wired_bool_twice_2.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/16/2014 04:04:57 AM
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
	char a,b,c,d;
	if( a | b && c | d )
		return 0;
	else
		return 1;
}
