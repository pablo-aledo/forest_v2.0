/*
 * =====================================================================================
 * /
 * |     Filename:  signal.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/08/2014 11:33:12 AM
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

#include <signal.h>
#include <stdio.h>

static void field_int(int sig){
	printf("hola\n");
}

int main() {

	signal(SIGINT, &field_int);

	while(1);
	
	return 0;
}
