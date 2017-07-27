/*
 * =====================================================================================
 * /
 * |     Filename:  for_infinite_loop_2.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/29/2014 05:02:25 PM
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
  int x;
  for(;;) {
	  if(x % 3 == 0 ) return 1;
	  if(x % 3 == 1 ) return 1;
	  if(x % 3 == 2 ) return 1;
  }
  return 0;
}
