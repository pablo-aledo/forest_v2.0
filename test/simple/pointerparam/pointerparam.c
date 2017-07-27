/*
 * =====================================================================================
 * /
 * |     Filename:  pointerparam.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/26/2013 10:14:50 AM
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


int function(int* value){
	if(value[5] == 0)
		return 0;
	else
		return 1;
}

int main() {

	int a[10][10];

	function(a[5]);
	
	return 0;
}
