/*
 * =====================================================================================
 * /
 * |     Filename:  strcmp_argv.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/11/2013 04:36:21 PM
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
#include <string.h>

int main(int argc, char *argv[])
{
	if(!strcmp(argv[0], "hello"))
		printf("hello\n");
	else
		printf("bye\n");
	return 0;
}
