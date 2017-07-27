/*
 * =====================================================================================
 * /
 * |     Filename:  ab.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/22/2014 06:37:25 PM
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
	
	float a,b;

ini:
	if(a < 0){ // C1
		b = a+1;
		if(b > 0){ // C2
			if(a > 0){ // C3
				return 1;
			}
			return 2;
		}

		return 3;
	}

	a = a - 5;

	goto ini;


	return 0;
}
