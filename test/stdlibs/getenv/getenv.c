/*
 * =====================================================================================
 * /
 * |     Filename:  getenv.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/17/2014 12:47:26 PM
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

extern "C" char *getenv(const char *name);
char** __environ;

int main () {

	char*  pointer1 = "PATH=hello";
	char*  pointer2 = 0;
	char* a[]= {pointer1, pointer2};
	__environ = a;

	char* pPath;
	pPath = getenv ("PATH");

	if ( pPath != 0 )
		return 1;
	else
		return 0;
}
