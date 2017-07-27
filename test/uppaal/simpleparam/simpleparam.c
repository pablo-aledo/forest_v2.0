/*
 * =====================================================================================
 * /
 * |     Filename:  simpleparam.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/29/2014 11:04:13 AM
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
	int param = *((int*)args);

	if(param == 1)
		k = k+1;
	else 
		k = k+2;

}

int main() {

	int a;

	pthread_t thread1;

	pthread_create(&thread1, NULL, &fn1, &a);

	return 0;
}



