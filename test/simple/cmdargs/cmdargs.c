/*
 * =====================================================================================
 * /
 * |     Filename:  cmdargs.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/13/2013 10:30:28 AM
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


int main(int argc, char *argv[]) {
	if(argv[1][1] == '-')
		return 0;
	else
		return 1;
}
