/*
 * =====================================================================================
 * /
 * |     Filename:  invalid_deref.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/29/2015 04:21:34 PM
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


int main() {
	char* a;
	char b = *(a+1);
	return 0;

}
