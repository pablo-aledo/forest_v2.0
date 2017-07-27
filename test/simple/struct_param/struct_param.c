/*
 * =====================================================================================
 * /
 * |     Filename:  struct.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/07/2013 07:45:56 AM
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

struct Estructura2{
	int a;
	int b;
};

struct Estructura {
	double entero1;
	int entero2;
	struct Estructura2 estructura3;
};

int function(struct Estructura a){

	return a.estructura3.a;

}

int main(){

	struct Estructura a;

	if( function(a) )
		return 0;
	else
		return 1;
}
