/*
 * =====================================================================================
 * /
 * |     Filename:  simple.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/25/2013 09:51:53 AM
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
int k;

void* fn1(void * args){

	wait(&a);

	if( k == 25 ){

		printf("hola\n");

	} else {

		printf("adios\n");

	}



}

void* fn2(void * args){

	k = 25;

	signal(&a);

}

int main() {

	/*pthread_mutex_lock(&a);*/

	pthread_t thread1, thread2;
	pthread_create(&thread1, NULL, &fn1, NULL);
	pthread_create(&thread2, NULL, &fn2, NULL);
	pthread_join(thread2, NULL);
	pthread_join(thread1, NULL);
	
	return 0;
}
