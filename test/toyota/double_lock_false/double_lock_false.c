/********Software Analysis - FY2013*************/
/*
* File Name: double_lock.c
* Defect Classification
* ---------------------
* Defect Type: Concurrency defects
* Defect Sub-type: Double lock
*
*/


/* #include <pthread.h>	Compile-time options. -lpthread You can specify */
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


/* Polyspace Does not support Concurrency */
#if defined(CHECKER_POLYSPACE)
# define NULL ((void *) 0)
int rand (void);
#endif /* defined(CHECKER_POLYSPACE) */
/*
 * Types of defects: double lock
 * Complexity: double-lock in same function using one thread
 */

pthread_mutex_t double_lock_001_glb_mutex = PTHREAD_MUTEX_INITIALIZER;

#if defined(CHECKER_POLYSPACE)
void double_lock_001_glb_mutex_lock () {}
void double_lock_001_glb_mutex_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */
#ifndef __NO_POLYSPACE__

int double_lock_001_glb_data = 0;

void* double_lock_001_tsk_001 (void *pram)
{
#if !defined(CHECKER_POLYSPACE)
	int ip = (int)pthread_self();
	pthread_mutex_lock(&double_lock_001_glb_mutex);
	double_lock_001_glb_data = (double_lock_001_glb_data % 100) + 1;
	pthread_mutex_lock(&double_lock_001_glb_mutex); 	/*Tool should detect this line as error*/ /*ERROR:Double Lock*/
	double_lock_001_glb_data = (double_lock_001_glb_data % 100) + 1;

    printf("Task1! It's me, thread #%d!\n",ip);

#endif /* #if defined(CHECKER_POLYSPACE) */
    return NULL;
}

void double_lock_001 ()
{
#if ! defined(CHECKER_POLYSPACE)
	pthread_t tid1;
	pthread_mutex_init(&double_lock_001_glb_mutex, NULL);
	pthread_create(&tid1, NULL, double_lock_001_tsk_001, NULL);
	pthread_join(tid1, NULL);
	pthread_mutex_destroy(&double_lock_001_glb_mutex);
#endif /* defined(CHECKER_POLYSPACE) */
}

#if defined(CHECKER_POLYSPACE)
void double_lock_001_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			double_lock_001_tsk_001(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: double lock
 * Complexity: Locking twice and unlocking only once in same function using one thread
 */
pthread_mutex_t double_lock_002_glb_mutex = PTHREAD_MUTEX_INITIALIZER;

#if defined(CHECKER_POLYSPACE)
void double_lock_002_glb_mutex_lock () {}
void double_lock_002_glb_mutex_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int double_lock_002_glb_data = 0;

void * double_lock_002_tsk_001 (void * pram)
{
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock (&double_lock_002_glb_mutex);
    double_lock_002_glb_data = (double_lock_002_glb_data% 100) + 1;
	/*Tool should detect this line as error*/
    pthread_mutex_lock (&double_lock_002_glb_mutex);  /*Tool should detect this line as error*/ /*ERROR:Double Lock*/
    double_lock_002_glb_data = (double_lock_002_glb_data% 100) + 1;
	pthread_mutex_unlock(&double_lock_002_glb_mutex);
#endif /* defined(CHECKER_POLYSPACE) */
   return NULL;
}

void double_lock_002 ()
{
#if !defined(CHECKER_POLYSPACE)
pthread_t tid1;
/* pthread_mutex_init (double_lock_002_glb_mutex, NULL); */
pthread_create (& tid1, NULL, double_lock_002_tsk_001, NULL);
pthread_join (tid1, NULL);
pthread_mutex_destroy (&double_lock_002_glb_mutex);
#endif /* defined(CHECKER_POLYSPACE) */
}

#if defined(CHECKER_POLYSPACE)
void double_lock_002_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			double_lock_002_tsk_001(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: double lock
 * Complexity: double-lock over multiple functions
 */
pthread_mutex_t double_lock_003_glb_mutex = PTHREAD_MUTEX_INITIALIZER;

#if defined(CHECKER_POLYSPACE)
void double_lock_003_glb_mutex_lock () {}
void double_lock_003_glb_mutex_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int double_lock_003_glb_data = 0;

void double_lock_003_func_001 ()
{
#if ! defined(CHECKER_POLYSPACE)
pthread_mutex_lock (&double_lock_003_glb_mutex); /*Tool should detect this line as error*/ /*ERROR:Double Lock*/
double_lock_003_glb_data = (double_lock_003_glb_data% 100) + 1;
/*pthread_mutex_unlock (&double_lock_003_glb_mutex);*/
#endif /* ! defined(CHECKER_POLYSPACE) */
}

void * double_lock_003_tsk_001 (void * pram)
{
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock (&double_lock_003_glb_mutex);
    double_lock_003_glb_data = (double_lock_003_glb_data% 100) + 1;

    double_lock_003_func_001 ();

    /*pthread_mutex_unlock (&double_lock_003_glb_mutex);*/
#endif /* ! defined(CHECKER_POLYSPACE) */
    return NULL;
}

void double_lock_003 ()
{
#if ! defined(CHECKER_POLYSPACE)
	pthread_t tid1;
    /* pthread_mutex_init (double_lock_003_glb_mutex, NULL); */
    pthread_create (& tid1, NULL, double_lock_003_tsk_001, NULL);
    pthread_join (tid1, NULL);
    pthread_mutex_destroy (&double_lock_003_glb_mutex);
#endif /* defined(CHECKER_POLYSPACE) */
}


#if defined(CHECKER_POLYSPACE)
void double_lock_003_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			double_lock_003_tsk_001(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: double lock
 * Complexity: double-lock over multiple functions using 2 threads
 */
pthread_mutex_t double_lock_004_glb_mutex1 = PTHREAD_MUTEX_INITIALIZER;

void *Thread3(void *input)
{
#if ! defined(CHECKER_POLYSPACE)
	long ip;

   pthread_mutex_lock( &double_lock_004_glb_mutex1 );
   ip = (long)input;
   ip = ip *10;
   printf("Task3! It's me, thread #%lu!\n",ip);
#endif /* defined(CHECKER_POLYSPACE) */
   return NULL;
}

void *Thread4(void *input)
{
#if ! defined(CHECKER_POLYSPACE)
	long ip;

   pthread_mutex_lock( &double_lock_004_glb_mutex1 ); /*Tool should detect this line as error*/ /*ERROR:Double Lock*/

   ip = (long)input;
   ip = ip *10;
   printf("Task4! It's me, thread #%lu!\n",ip);
#endif /* defined(CHECKER_POLYSPACE) */
   return NULL;
}

void double_lock_004 ()
{
#if ! defined(CHECKER_POLYSPACE)
	   pthread_t th1,th2;
	   int rc = 1;
	   long int t1 = 10;
	   long int t2 = 20;
	   sink += pthread_create(&th1, NULL, Thread3, (void *)t1);
	   sink += pthread_create(&th2, NULL, Thread4, (void *)t2);
#endif /* defined(CHECKER_POLYSPACE) */
}

/*
 * Types of defects: double lock
 * double lock main function
 */
extern volatile int vflag;
void double_lock_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		double_lock_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		double_lock_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		double_lock_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		double_lock_004();
	}
}
#endif
