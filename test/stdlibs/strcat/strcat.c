/*
 * =====================================================================================
 * /
 * |     Filename:  strcat.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/11/2014 04:00:26 AM
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


extern "C" char *strcat(char * dest, const char * src);

char a[11] = "hello";
char b[ 6] = "world";

int main() {

	strcat(a,b);

	if(a[8] == 'z')
		return 0;
	else
		return 1;
}
