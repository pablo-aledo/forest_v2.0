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

#define ITERS 3

#define wait(m) pthread_mutex_lock(m);
#define signal(m) pthread_mutex_unlock(m);

pthread_mutex_t mutex1, mutex2;

//int array[BUFFER_SIZE];
//long long int sum=0;
int sum=0;

void* consumer(void * arg)
{
        
	int i=0;
        for(i = 0; i < ITERS; i++)
        {
		wait(&mutex1);                
                //sum += array[i%BUFFER_SIZE];
		sum -= 1;
             
		signal(&mutex2);
        }
        return NULL;
}

void* producer(void * arg)//productor
{
	int i=0;
        for(i = 0; i < ITERS; i++)
        {
		wait(&mutex2);
                sum += 1;
                signal(&mutex1);
                
        }
        return NULL;
}


int main() {
	wait(&mutex1);
        pthread_t t1,t2;
 
        pthread_create(&t1,NULL,&consumer,NULL);
        pthread_create(&t2,NULL,&producer,NULL);
        pthread_join(t1,NULL);
        pthread_join(t2,NULL);
        return 0;
}

