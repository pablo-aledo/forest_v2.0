/*
 * =====================================================================================
 * /
 * |     Filename:  recursive.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/02/2015 02:36:25 AM
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


int fn(int x){
	if(x == 1) return 0;
	else return fn(x-1);
}

int main() {
	int x;
	if(x >= 3 || x <= 0) return 0;
	return fn(x);
}
