/********Software Analysis - FY2013*************/
/*
* File Name: data_lost.c
* Defect Classification
* ---------------------
* Defect Type: Concurrency defects
* Defect Sub-type: Live lock
* Description: Defect Free Code to identify false positives in live lock - concurrency conditions
*/


/* Livelock
 * Complexity: Thread 1 and thread 2 try to give up the 
 * control of the thread.This leads to the system not progressing further.
 */

/*
 * HeaderFile.h
 *
 */

#ifndef HEADERFILE_H_
#define HEADERFILE_H_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <pthread.h>
#include <ctype.h>
#include <unistd.h>
#include <limits.h>

extern int idx, sink;
extern double dsink;
extern void *psink;

void bit_shift_main (void);
void dynamic_buffer_overrun_main (void);
void dynamic_buffer_underrun_main (void);
void cmp_funcadr_main (void);
void conflicting_cond_main (void);
void data_lost_main (void);
void data_overflow_main (void);
void data_underflow_main (void);
void dead_code_main (void);
void dead_lock_main (void);
void deletion_of_data_structure_sentinel_main (void);
void double_free_main (void);
void double_lock_main (void);
void double_release_main (void);
void endless_loop_main (void);
void free_nondynamic_allocated_memory_main (void);
void free_null_pointer_main (void);
void func_pointer_main (void);
void function_return_value_unchecked_main (void);
void improper_termination_of_block_main (void);
void insign_code_main (void);
void invalid_extern_main (void);
void invalid_memory_access_main (void);
void littlemem_st_main (void);
void livelock_main (void);
void lock_never_unlock_main  (void);
void memory_allocation_failure_main(void);
void memory_leak_main (void);
void not_return_main (void);
void null_pointer_main (void);
void overrun_st_main (void);
void ow_memcpy_main (void);
void pow_related_errors_main (void);
void ptr_subtraction_main (void);
void race_condition_main (void);
void redundant_cond_main (void);
void return_local_main (void);
void sign_conv_main (void);
void sleep_lock_main (void);
void st_cross_thread_access_main (void);
void st_overflow_main (void);
void st_underrun_main (void);
void underrun_st_main (void);
void uninit_memory_access_main (void);
void uninit_pointer_main (void);
void uninit_var_main (void);
void unlock_without_lock_main (void);
void unused_var_main (void);
void wrong_arguments_func_pointer_main (void);
void zero_division_main (void);

/*
# define PRINT_DEBUG 0
*/

#endif /* HEADERFILE_H_ */

pthread_mutex_t livelock_001_glb_A;
pthread_mutex_t livelock_001_glb_B;

int x,y;

void *mythreadA(void *pram)
{
	while(1)
	{
		pthread_mutex_lock(&livelock_001_glb_A);
		x=x+1;
		pthread_mutex_unlock(&livelock_001_glb_A);
		int status=pthread_mutex_trylock(&livelock_001_glb_B);
		pthread_mutex_unlock(&livelock_001_glb_B);

		if(status==0)
		{
			break;
		}
	}
    return NULL;
}

void *mythreadB(void *pram)
{
	while(1)
	{
		pthread_mutex_lock(&livelock_001_glb_B);
		y=y+1;
		pthread_mutex_unlock(&livelock_001_glb_B);

		int status=pthread_mutex_trylock(&livelock_001_glb_A);
		pthread_mutex_unlock(&livelock_001_glb_A);
		if(status==0)
		{
			break;
		}
	}
    return NULL;
}

void livelock_001()
{
	pthread_t pthreadA,pthreadB;

	pthread_mutex_init(&livelock_001_glb_A,NULL);
	pthread_mutex_init(&livelock_001_glb_B,NULL);

	pthread_create(&pthreadA,NULL,mythreadA,NULL);
	pthread_create(&pthreadB,NULL,(void *) &mythreadB,NULL);

	pthread_join(pthreadA,NULL);
	pthread_join(pthreadB,NULL);
		
}

extern volatile int vflag;
void livelock_main ()
{

	if (vflag> 0)
	{
		livelock_001 ();
	}

}
