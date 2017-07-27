/*
 * =====================================================================================
 * /
 * |     Filename:  globalstruct.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  31/07/2013 08:45:57 AM
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

struct Estructura3 {
	int entero4;
	int entero5;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura3 estructura3;
};

struct Estructura a;

int main(){

	if( a.estructura3.entero5 > 0 )
		return 0;
	else
		return 1;
}
