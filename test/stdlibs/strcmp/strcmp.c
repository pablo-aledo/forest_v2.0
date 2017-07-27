/*
 * =====================================================================================
 * /
 * |     Filename:  strcmp.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/11/2014 04:52:11 AM
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


extern "C" int strcmp(char* s1, char* s2);

char a[] = "hello";
char b[] = "world";

int main() {
	int c = strcmp(a,b);
	if(c > 0)
		return 0;
	else if( c < 0 )
		return 1;
	else if( c == 0 )
		return 2;
}
