/*
 * =====================================================================================
 * /
 * |     Filename:  doublefree.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/05/2015 02:39:01 PM
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
	char* a = (char*)fr_malloc(5);
	fr_free(a);
	fr_free(a);
	return 0;
}
