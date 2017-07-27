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


typedef struct getopt_data
{
	char *optarg;
	int optind, optwhere;
} getopt_data;


int main() {

	struct getopt_data data;
	if (data.optwhere == 5)
		return 5;
	return 0;
}
