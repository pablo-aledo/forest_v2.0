/********Software Analysis - FY2013*************/
/*
* File Name: sleep_lock.c
* Defect Classification
* ---------------------
* Defect Type: Concurrency defects
* Defect Sub-type: Long lock
* Description: Defect Free Code to identify false positives of long lock conditions
*/
/***
#include <pthread.h>	 Compile-time options. -lpthread You can specify*/

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


#if defined(CHECKER_POLYSPACE)
int rand (void);
#endif /* defined(CHECKER_POLYSPACE) */
/*
 * Types of defects: long lock time
 * Complexity: long time sleep
 */
pthread_mutex_t sleep_lock_001_glb_mutex_;
pthread_mutex_t *sleep_lock_001_glb_mutex = &sleep_lock_001_glb_mutex_;
/* #if defined(CHECKER_POLYSPACE) */
void sleep_lock_001_glb_mutex_lock () {}
void sleep_lock_001_glb_mutex_unlock () {}
/* #endif  #if defined(CHECKER_POLYSPACE) */

int sleep_lock_001_glb_data = 0;

void* sleep_lock_001_tsk_001 (void *pram)
{
	pthread_mutex_lock(sleep_lock_001_glb_mutex);
	sleep_lock_001_glb_data = (sleep_lock_001_glb_data % 100) + 1;

    /*Tool should not detect this line as error*/ /*No Error:Long Sleep */

	pthread_mutex_unlock(sleep_lock_001_glb_mutex);
	return NULL;
}

void sleep_lock_001 ()
{
	pthread_t tid1;
	pthread_mutex_init(sleep_lock_001_glb_mutex, NULL);
	pthread_create(&tid1, NULL, sleep_lock_001_tsk_001, NULL);
	pthread_join(tid1, NULL);
	pthread_mutex_destroy(sleep_lock_001_glb_mutex);
}

#if defined(CHECKER_POLYSPACE)
void sleep_lock_001_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			sleep_lock_001_tsk_001(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: long lock time
 * Complexity: wait socket
 */
int sleep_lock_002_glb_data = 0;
pthread_mutex_t sleep_lock_002_glb_mutex_;
pthread_mutex_t *sleep_lock_002_glb_mutex = &sleep_lock_002_glb_mutex_;
void* sleep_lock_002_tsk_001 (void *pram)
{
	pthread_mutex_lock(sleep_lock_002_glb_mutex);
	sleep_lock_002_glb_data = (sleep_lock_002_glb_data % 100) + 1;
    /*Tool should not detect this line as error*/ /*No Error:Long Sleep */
	pthread_mutex_unlock(sleep_lock_002_glb_mutex);
	return NULL;
}

void sleep_lock_002 ()
{
	pthread_t tid1;
	pthread_mutex_init(sleep_lock_002_glb_mutex, NULL);
	pthread_create(&tid1, NULL, sleep_lock_002_tsk_001, NULL);
	pthread_join(tid1, NULL);
	pthread_mutex_destroy(sleep_lock_002_glb_mutex);
}

/*
 * Types of defects: long lock time
 * Complexity: across the function long time sleep
 */
pthread_mutex_t sleep_lock_003_glb_mutex_;
pthread_mutex_t *sleep_lock_003_glb_mutex = &sleep_lock_003_glb_mutex_;
#if defined(CHECKER_POLYSPACE)
void sleep_lock_003_glb_mutex_lock () {}
void sleep_lock_003_glb_mutex_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int sleep_lock_003_glb_data = 0;

void sleep_lock_003_func_001 ()
{
	/* Do nothing */
    /*Tool should not detect this line as error*/ /*No Error:Long Sleep */
}

void* sleep_lock_003_tsk_001 (void *pram)
{
	pthread_mutex_lock(sleep_lock_003_glb_mutex);
	sleep_lock_003_glb_data = (sleep_lock_003_glb_data % 100) + 1;

	sleep_lock_003_func_001();

	pthread_mutex_unlock(sleep_lock_003_glb_mutex);
	return NULL;
}

void sleep_lock_003 ()
{
	pthread_t tid1;
	pthread_mutex_init(sleep_lock_003_glb_mutex, NULL);
	pthread_create(&tid1, NULL, sleep_lock_003_tsk_001, NULL);
	pthread_join(tid1, NULL);
	pthread_mutex_destroy(sleep_lock_003_glb_mutex);
}

#if defined(CHECKER_POLYSPACE)
void sleep_lock_003_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			sleep_lock_003_tsk_001(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: long lock time
 * long time sleep Main function
 */
extern volatile int vflag;
void sleep_lock_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		sleep_lock_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		sleep_lock_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		sleep_lock_003();
	}
}
