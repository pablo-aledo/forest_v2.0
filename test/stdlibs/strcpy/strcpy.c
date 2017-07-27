/*
 * =====================================================================================
 * /
 * |     Filename:  strcpy.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/10/2014 12:47:29 PM
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

extern "C" char *strcpy(char *dest, const char *src);

int main() {

	char src[] = "hello";
	char dst[] = "world";

	strcpy(dst, src);

	if(dst[1] == 'a')
		return 0;
	else
		return 1;
}
