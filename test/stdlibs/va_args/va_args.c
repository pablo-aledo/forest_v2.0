/*
 * =====================================================================================
 * /
 * |     Filename:  va_args.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/08/2014 01:18:16 PM
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

#include <stdarg.h>


int prod (int n_ptrs, ...) {
	va_list ap;
	int prod = 1;
	va_start(ap, n_ptrs);
	for ( ; n_ptrs; n_ptrs--) {
		prod *= va_arg(ap, int );
	}
	va_end(ap);

	return prod;
}


int main() {
	
	if(prod(2,2,3) == 6)
		return 1;
	else
		return 0;

}
