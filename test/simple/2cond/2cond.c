/*
 * =====================================================================================
 * /
 * |     Filename:  2cond.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/11/2014 09:33:49 AM
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

int gcd(int a, int b){

	if(a){
		if(b){
			return 0;
		} else {
			return 1;
		}
	} else {
		if(b){
			return 1;
		} else {
			return 2;
		}
	}
}

int main() {
}
