/*
 * =====================================================================================
 * /
 * |     Filename:  alloc_range.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/02/2015 12:26:06 PM
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

extern "C" void* fr_malloc(unsigned long size);

int main() {
	int x;
	int y;
	if( (x-4)*(x-4) - 9 > 0 ) return 0;
	if( (y-6)*(y-6) - 9 > 0 ) return 0;
	// x in range [1,7]
	// y in range [2,9]
	char* a = (char*)fr_malloc(x);
	if(a[y])
		return 0;
	else
		return 1;
}
