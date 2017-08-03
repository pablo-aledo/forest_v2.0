/*
 * =====================================================================================
 * /
 * |     Filename:  isolate_with_pointers.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  08/03/2017 11:01:21 AM
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

struct c{
	int e[10];
};

struct a {
	int b;
	struct c* d;
};

int fn( struct a* x ){
	return 0;
}

int main()
{
	struct a x;
	fn(&x);
	return 0;
}
