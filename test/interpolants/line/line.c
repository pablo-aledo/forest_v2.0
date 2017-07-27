/*
 * =====================================================================================
 * /
 * |     Filename:  line.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/19/2014 12:01:23 AM
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
	int a,b,c;

	if(a > 0){
l1:
		a = a+1;
l2:
		b = 2*a;
l3:
		c = 5;
l4:
		if(b < 0){
			return 0;
		} else {
			return 1;
		}
	}

	return 1;
}
