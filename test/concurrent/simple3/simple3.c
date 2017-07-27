/*
 * =====================================================================================
 * /
 * |     Filename:  simple2.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/25/2013 11:41:45 AM
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
/*inline void wait(pthread_mutex_t* m){ pthread_mutex_lock(m); }*/
/*inline void signal(pthread_mutex_t* m){ pthread_mutex_unlock(m); }*/

pthread_mutex_t a;
pthread_mutex_t b;
pthread_mutex_t c;

int k;
int j;

void* fn1(void * args){

	wait(&a);

	if( k == 25 ){

		wait(&b);

		j = 1-j;

		if( j )
			printf("hola\n");
		else
			printf("adios\n");

	} else {
		wait(&c);
	}



}

void* fn2(void * args){

	signal(&a);

	if( k == 12 ){
		j = 1;
		signal(&b);
	} else {
		j = 0;
		signal(&b);
		signal(&c);
	}


}

int main() {

	pthread_t thread1;
	pthread_t thread2;

	pthread_create(&thread1, NULL, &fn1, NULL);
	pthread_create(&thread2, NULL, &fn2, NULL);

	pthread_join(thread1, NULL);
	pthread_join(thread2, NULL);
	
	return 0;
}

