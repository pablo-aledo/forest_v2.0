/*
 * =====================================================================================
 * /
 * |     Filename:  non_annotated_twice.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/03/2013 10:03:33 AM
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
	if( printf("hola") ){
		if( printf("adios") ){
			return 1;
		} else {
			return 2;
		}
	} else {
		return 3;
	}

	return 4;
}
