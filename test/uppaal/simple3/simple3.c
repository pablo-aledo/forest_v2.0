/*
 * =====================================================================================
 * /
 * |     Filename:  simple3.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/19/2014 11:17:08 AM
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

	int k;

	k = 1;

	wait(&a);

	while( k < 100 ){

		if( k < 50 ){
			signal(&a);
		} else {
			wait(&a);
		}

		k++;

	}

	wait(&a);



}

int main() {

	pthread_t thread1;

	pthread_create(&thread1, NULL, &fn1, NULL);

	return 0;
}






