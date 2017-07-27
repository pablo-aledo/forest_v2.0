/*
 * =====================================================================================
 * /
 * |     Filename:  force_free_global_array.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/13/2014 06:22:35 AM
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


int array[5];

int main() {
	if(array[1]) return 0;
	else return 1;
}
