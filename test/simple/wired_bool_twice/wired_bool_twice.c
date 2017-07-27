/*
 * =====================================================================================
 * /
 * |     Filename:  wired_bool_twice.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/15/2014 06:07:58 PM
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
	if( a & b && c & d )
		return 1;
	else
		return 0;
}
