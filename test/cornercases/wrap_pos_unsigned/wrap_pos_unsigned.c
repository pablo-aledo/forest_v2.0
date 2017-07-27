/*
 * =====================================================================================
 * /
 * |     Filename:  wrap_pos.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/31/2014 02:56:09 AM
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
	unsigned char a = 120;
	unsigned char i;
	unsigned char b = a + i;

	if( b == 130 ) return 1;

	return 2;
}
