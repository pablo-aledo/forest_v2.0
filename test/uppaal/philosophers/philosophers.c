/*
 * =====================================================================================
 * /
 * |     Filename:  philosophers.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/11/2014 04:27:35 PM
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

#define N 5                                 // number of philosophers
#define IZQ (i+4)%N
#define DER (i+1)%N
#define THINKING 0
#define HUNGRY 1
#define EATING 2


pthread_t philosophers[N];                                         // threads representing philosophers
pthread_mutex_t mutex ;                                            // semaphore for the critical section
pthread_mutex_t s[N];                                              // semaphores for the philosophers
int state[N] = {THINKING, THINKING, THINKING, THINKING, THINKING}; // state of each philosopher

void think(int i) {
	state[i] = THINKING;
}

void eat(int i) {
	state[i] = EATING;
}

void check_forks(int i) {
	if(state[i]==HUNGRY &&state[IZQ]!=EATING &&state[DER]!=EATING ){
		state[i] = EATING;
		pthread_mutex_unlock(&s[i]);
	}
}

void take_forks(int i) {
	pthread_mutex_lock(&mutex);         // enter critical section using semaphore
	state[i] = HUNGRY;                  // notifies he's hungry 
	check_forks(i);                     // checks that he can take the forks
	pthread_mutex_unlock(&mutex);       // allows others to enter
	pthread_mutex_lock(&s[i]);          // blocks if he can not take the forks
}

void leave_forks(int i) {

	pthread_mutex_lock(&mutex);  // enters critical section 
	state[i] = THINKING;         // stops eating and start thinking
	check_forks(IZQ);        
	check_forks(DER);
	pthread_mutex_unlock(&mutex);
}

void * philosophers_fn(void * args) {
	/*int i= *((int*)args);*/
	int i = 0;


	for (;;) {
		think(i) ;
		take_forks(i) ;
		eat(i) ;
		leave_forks(i) ;
	}
}


main() {

	int i;

	for (i=0; i<N; i++){
		pthread_create(& philosophers[i], NULL, &philosophers_fn,(void *)i);
	}

	for (i=0; i<N; i++){
		pthread_join( philosophers[i],NULL);
	}

}
