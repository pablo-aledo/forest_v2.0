/*
 * =====================================================================================
 * /
 * |     Filename:  alloc_iter_free.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/22/2015 12:01:10 PM
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
extern "C" void  fr_free  (void* pointer);

int main() {

	char* x = (char*)fr_malloc(5);
	x++;
	x--;
	fr_free(x);
	return 0;
}

