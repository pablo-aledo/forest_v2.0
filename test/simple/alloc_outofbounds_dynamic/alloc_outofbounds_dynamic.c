/*
 * =====================================================================================
 * /
 * |     Filename:  alloc_outofbounds_dynamic.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/02/2015 10:44:49 AM
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
	int b;
	char* a = (char*)fr_malloc(5);
	if(b > 5) return 0;
	if(a[b])
		return 0;
	else
		return 1;
}
