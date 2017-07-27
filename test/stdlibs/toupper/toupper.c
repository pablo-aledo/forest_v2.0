/*
 * =====================================================================================
 * /
 * |     Filename:  tolower.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/06/2014 03:04:38 PM
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

extern "C" int toupper(int a);

int main() {

	int x = 'a';

	if(toupper(x) == 'A')
		return 0;
	else
		return 1;
}
