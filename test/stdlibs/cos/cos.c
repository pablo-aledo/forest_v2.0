/*
 * =====================================================================================
 * /
 * |     Filename:  cos.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/07/2014 03:54:30 PM
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


extern "C" double cos(double x);

int main() {

	/*double x = 0;*/
	double x = 3.1416;

	double y = cos(x);

	if( y > 0)
		return 0;
	else
		return 1;
}
