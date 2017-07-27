/*
 * =====================================================================================
 * /
 * |     Filename:  arraysem.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/01/2014 06:33:49 AM
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
pthread_mutex_t b;
pthread_mutex_t c;
pthread_mutex_t* array[5] = {&a,&b,&c,&a,&c};

void* fn1(void * args){

	int x,k,j;

	wait(array[j]);

	if( x < 0 ){
		signal(array[k]);
		j++;
	} else {
		wait(array[x]);
	}

	wait(&b);


}

int main() {

	pthread_t thread1;

	pthread_create(&thread1, NULL, &fn1, NULL);

	return 0;
}




