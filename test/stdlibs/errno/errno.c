/*
 * =====================================================================================
 * /
 * |     Filename:  errno.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/06/2014 04:42:19 PM
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

#   define errno (*__errno_location ())
#define __THROW 
extern int *__errno_location (void) __THROW __attribute__ ((__const__));
/*extern "C" double sqrt(double x);*/

int main() {

	int x = -1;
	
	errno = 0;
	sqrt(x);
	if(errno)
		return 0;
	else
		return 1;
}
