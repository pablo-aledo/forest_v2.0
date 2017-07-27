/*
 * =====================================================================================
 * /
 * |     Filename:  simple.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/15/2014 03:15:37 AM
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

int complex_condition(){

	int a;

	if( a * a < 0)
		return 0;
	else
		return 1;
}


int main() { 

	int c;
	int j;

	for ( int i = 0; i < 5; i++) {
		if(c < i){
			j = 0;
			break;
		} else {
			j = 1;
		}
	}

	return complex_condition();

}
