/*
 * =====================================================================================
 * /
 * |     Filename:  getopt.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/20/2013 03:10:42 PM
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


int getopt (const char *optstring) {

	if(optstring == 0) return 0;
	return 1;
}

int main() {


	getopt("nt:");
	return 0;
}

