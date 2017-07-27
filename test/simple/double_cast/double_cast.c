/*
 * =====================================================================================
 * /
 * |     Filename:  double_cast.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/11/2014 08:54:11 AM
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
	float a;
	int b = a;
	float c = b;
	if(c == 5.5)
		return 0;
	else
		return 1;
}
