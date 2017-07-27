/*
 * =====================================================================================
 * /
 * |     Filename:  setlocale.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/07/2014 12:58:24 PM
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


#include <locale.h>

int main() {

	/*char local[6] = "C";*/
	char local[6] = "";

	setlocale(LC_ALL, local);

	struct lconv *p = localeconv();
	char* cur_sym = p->mon_decimal_point;

	if(*cur_sym == '.')
		return 0;
	else
		return 1;
}
