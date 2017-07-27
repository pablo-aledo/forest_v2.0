/*
 * =====================================================================================
 * /
 * |     Filename:  alloc_int.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/29/2015 04:26:06 PM
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
	int* a = (int*)fr_malloc(5);
	if(a[1])
		return 0;
	else
		return 1;
}
