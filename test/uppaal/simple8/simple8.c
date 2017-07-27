/*
 * =====================================================================================
 * /
 * |     Filename:  simple8.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/26/2014 04:59:51 PM
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

#include <pthread.h>
#include <stdio.h>

#define wait(m) pthread_mutex_lock(m);
#define signal(m) pthread_mutex_unlock(m);

pthread_mutex_t a;

void* fn1(void * args){

	int x, l, j, k;

	x = 0;
	l = 0;

	wait(&a);

	j = 0;

	if( k != 25 ){

		if( k == 21 ){
			signal(&a);
		} else {

		}

	} else {

		k = 13;
		wait(&a);

	}

	wait(&a);

	k=((k+k)*((l+l)*3))+5;
	l++;


}

int main() {

	pthread_t thread1;

	pthread_create(&thread1, NULL, &fn1, NULL);

	return 0;
}



