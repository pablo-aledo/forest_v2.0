/*
 * =====================================================================================
 * /
 * |     Filename:  unsigned_uneq.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/01/2014 12:31:40 PM
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

	unsigned char au = 120;
	char as = 120;


	unsigned char bu;// = 130;
	         char bs;// = 130;


	if( (char)bu == (char)bs && au < bu && as > bs )
		return 1;
	
	return 0;
}
