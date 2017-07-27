/*
 * =====================================================================================
 * /
 * |     Filename:  offsetof.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/08/2014 02:49:44 PM
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

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

int main() {
	struct s {
		int i;
		char c;
		double d;
		char a[];
	};

	printf("offsets: i=%ld; c=%ld; d=%ld a=%ld\n",
			(long) offsetof(struct s, i),
			(long) offsetof(struct s, c),
			(long) offsetof(struct s, d),
			(long) offsetof(struct s, a));
	printf("sizeof(struct s)=%ld\n", (long) sizeof(struct s));

	exit(EXIT_SUCCESS);
}






