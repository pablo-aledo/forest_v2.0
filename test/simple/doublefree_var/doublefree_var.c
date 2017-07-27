/*
 * =====================================================================================
 * /
 * |     Filename:  doublefree_var.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/05/2015 04:34:44 PM
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
	int b;
	if(b < 0 || b > 1) return 0;
	char* c = a+b;
	fr_free(c);
	return 0;
}

