/*
 * =====================================================================================
 * /
 * |     Filename:  basename.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/11/2014 05:09:10 AM
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


extern "C" char *basename(char *s);

int main() {
	char a[] = "/a/";
	basename(a);
	return 0;
}
