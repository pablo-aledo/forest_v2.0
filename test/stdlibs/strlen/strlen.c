/*
 * =====================================================================================
 * /
 * |     Filename:  strlen.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/11/2014 03:23:02 AM
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


extern "C" int strlen(char *str);

int main() {
	char str[] = "hello";
	if(strlen(str) == 3)
		return 0;
	else if(strlen(str) == 4)
		return 1;
	return 2;
}
