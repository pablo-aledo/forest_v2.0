/*
 * =====================================================================================
 * /
 * |     Filename:  isalpha.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/13/2014 10:13:12 AM
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

extern "C" int isdigit(int c);

int main() {
	int c;
	if(isdigit(c))
		return 0;
	else
		return 1;
}
