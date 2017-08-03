/*
 * =====================================================================================
 * /
 * |     Filename:  isolate_and_pointer.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/01/2017 04:10:30 PM
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


void fn(int* a){
	a[1] = 2;
}

int main() {
	return 0;
}
