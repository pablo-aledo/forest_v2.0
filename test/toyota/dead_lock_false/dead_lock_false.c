/********Software Analysis - FY2013*************/
/*
* File Name: dead_lock.c
* Defect Classification
* ---------------------
* Defect Type: Concurrency defects
* Defect Sub-type: Dead lock
*
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

#if defined(CHECKER_POLYSPACE)
int rand (void);
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Complexity: exclusive control of two resources task 1: A -> B, task 2: B -> A
 */
pthread_mutex_t dead_lock_001_glb_mutexA = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t dead_lock_001_glb_mutexB = PTHREAD_MUTEX_INITIALIZER;
#if defined(CHECKER_POLYSPACE)
void dead_lock_001_glb_mutexA_lock () {}
void dead_lock_001_glb_mutexA_unlock () {}
void dead_lock_001_glb_mutexB_lock () {}
void dead_lock_001_glb_mutexB_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int dead_lock_001_glb_dataA = 10;
int dead_lock_001_glb_dataB = 10;

void* dead_lock_001_tsk_001 (void *pram)
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_001_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_001_glb_dataA = (dead_lock_001_glb_dataA % 100) + 10;
    printf("Task1! dead_lock= %d \n",dead_lock_001_glb_dataA);

	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_001_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_001_glb_dataB = (dead_lock_001_glb_dataB % 100) + 20;

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_001_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_001_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_001_tsk_002 (void *pram)
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_001_glb_mutexB);  /*Tool should detect this line as error*/ /*ERROR:Dead Lock*/
#endif /* ! defined(CHECKER_POLYSPACE) */

	dead_lock_001_glb_dataA = (dead_lock_001_glb_dataA % 100) + 1;

	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_001_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */

	dead_lock_001_glb_dataB = (dead_lock_001_glb_dataB % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_001_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_001_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void dead_lock_001 ()
{
	pthread_t tid1;
	pthread_t tid2;

	pthread_mutex_init(&dead_lock_001_glb_mutexA, NULL);
	pthread_mutex_init(&dead_lock_001_glb_mutexB, NULL);

	pthread_create(&tid1, NULL, dead_lock_001_tsk_001, NULL);
	pthread_create(&tid2, NULL, dead_lock_001_tsk_002, NULL);

	pthread_join(tid1, NULL);
	pthread_join(tid2, NULL);

	pthread_mutex_destroy(&dead_lock_001_glb_mutexA);
	pthread_mutex_destroy(&dead_lock_001_glb_mutexB);
}

#if defined(CHECKER_POLYSPACE)
void dead_lock_001_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_001_tsk_001(NULL);
		}
	}
}

void dead_lock_001_tskentry_002 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_001_tsk_002(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Complexity: exclusive control three resources task 1: A -> B, task 2: B -> C and task 3: C -> A
 */

pthread_mutex_t dead_lock_002_glb_mutexA = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t dead_lock_002_glb_mutexB = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t dead_lock_002_glb_mutexC = PTHREAD_MUTEX_INITIALIZER;
#if defined(CHECKER_POLYSPACE)
void dead_lock_002_glb_mutexA_lock () {}
void dead_lock_002_glb_mutexA_unlock () {}
void dead_lock_002_glb_mutexB_lock () {}
void dead_lock_002_glb_mutexB_unlock () {}
void dead_lock_002_glb_mutexC_lock () {}
void dead_lock_002_glb_mutexC_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int dead_lock_002_glb_dataA = 0;
int dead_lock_002_glb_dataB = 0;
int dead_lock_002_glb_dataC = 0;

void* dead_lock_002_tsk_001 (void *pram)
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataA = (dead_lock_002_glb_dataA % 100) + 1;

	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataB = (dead_lock_002_glb_dataB % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_002_tsk_002 (void *pram)
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataB = (dead_lock_002_glb_dataB % 100) + 1;

	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexC);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataC = (dead_lock_002_glb_dataC % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexC);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexB);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_002_tsk_003 (void *pram)
{
	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexC); /*Tool should detect this line as error*/ /*ERROR:Dead Lock*/
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataC = (dead_lock_002_glb_dataC % 100) + 1;

	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(&dead_lock_002_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_002_glb_dataA = (dead_lock_002_glb_dataA % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexA);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(&dead_lock_002_glb_mutexC);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void dead_lock_002 ()
{
	pthread_t tid1;
	pthread_t tid2;
	pthread_t tid3;

	pthread_mutex_init(&dead_lock_002_glb_mutexA, NULL);
	pthread_mutex_init(&dead_lock_002_glb_mutexB, NULL);
	pthread_mutex_init(&dead_lock_002_glb_mutexC, NULL);

	pthread_create(&tid1, NULL, dead_lock_002_tsk_001, NULL);
	pthread_create(&tid2, NULL, dead_lock_002_tsk_002, NULL);
	pthread_create(&tid3, NULL, dead_lock_002_tsk_003, NULL);

	pthread_join(tid1, NULL);
	pthread_join(tid2, NULL);
	pthread_join(tid3, NULL);

	pthread_mutex_destroy(&dead_lock_002_glb_mutexA);
	pthread_mutex_destroy(&dead_lock_002_glb_mutexB);
	pthread_mutex_destroy(&dead_lock_002_glb_mutexC);
}

#if defined(CHECKER_POLYSPACE)
void dead_lock_002_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_002_tsk_001(NULL);
		}
	}
}

void dead_lock_002_tskentry_002 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_002_tsk_002(NULL);
		}
	}
}

void dead_lock_002_tskentry_003 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_002_tsk_003(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Complexity: exclusive control three resources task 1: A -> B -> C, task 2: B -> A -> C
 */
pthread_mutex_t dead_lock_003_glb_mutexA_;
pthread_mutex_t dead_lock_003_glb_mutexB_;
pthread_mutex_t dead_lock_003_glb_mutexC_;
pthread_mutex_t *dead_lock_003_glb_mutexA = &dead_lock_003_glb_mutexA_;
pthread_mutex_t *dead_lock_003_glb_mutexB = &dead_lock_003_glb_mutexB_;
pthread_mutex_t *dead_lock_003_glb_mutexC = &dead_lock_003_glb_mutexC_;
#if defined(CHECKER_POLYSPACE)
void dead_lock_003_glb_mutexA_lock () {}
void dead_lock_003_glb_mutexA_unlock () {}
void dead_lock_003_glb_mutexB_lock () {}
void dead_lock_003_glb_mutexB_unlock () {}
void dead_lock_003_glb_mutexC_lock () {}
void dead_lock_003_glb_mutexC_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int dead_lock_003_glb_dataA = 0;
int dead_lock_003_glb_dataB = 0;
int dead_lock_003_glb_dataC = 0;

void* dead_lock_003_tsk_001 (void *pram)
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataA = (dead_lock_003_glb_dataA % 100) + 1;

	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataB = (dead_lock_003_glb_dataB % 100) + 1;

	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataC = (dead_lock_003_glb_dataC % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_003_tsk_002 (void *pram)
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexB);/*Tool should detect this line as error*/ /*ERROR:Dead Lock*/
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataB = (dead_lock_003_glb_dataB % 100) + 1;

	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataA = (dead_lock_003_glb_dataA % 100) + 1;

	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_003_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_003_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_003_glb_dataC = (dead_lock_003_glb_dataC % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_003_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_003_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void dead_lock_003 ()
{
	pthread_t tid1;
	pthread_t tid2;

	pthread_mutex_init(dead_lock_003_glb_mutexA, NULL);
	pthread_mutex_init(dead_lock_003_glb_mutexB, NULL);
	pthread_mutex_init(dead_lock_003_glb_mutexC, NULL);

	pthread_create(&tid1, NULL, dead_lock_003_tsk_001, NULL);
	pthread_create(&tid2, NULL, dead_lock_003_tsk_002, NULL);

	pthread_join(tid1, NULL);
	pthread_join(tid2, NULL);

	pthread_mutex_destroy(dead_lock_003_glb_mutexA);
	pthread_mutex_destroy(dead_lock_003_glb_mutexB);
	pthread_mutex_destroy(dead_lock_003_glb_mutexC);
}

#if defined(CHECKER_POLYSPACE)
void dead_lock_003_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_003_tsk_001(NULL);
		}
	}
}

void dead_lock_003_tskentry_002 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_003_tsk_002(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Complexity: exclusive control three resources task 1: A -> B -> C, task 2: B -> C -> A
 */
pthread_mutex_t dead_lock_004_glb_mutexA_;
pthread_mutex_t dead_lock_004_glb_mutexB_;
pthread_mutex_t dead_lock_004_glb_mutexC_;
pthread_mutex_t *dead_lock_004_glb_mutexA = &dead_lock_004_glb_mutexA_;
pthread_mutex_t *dead_lock_004_glb_mutexB = &dead_lock_004_glb_mutexB_;
pthread_mutex_t *dead_lock_004_glb_mutexC = &dead_lock_004_glb_mutexC_;
#if defined(CHECKER_POLYSPACE)
void dead_lock_004_glb_mutexA_lock () {}
void dead_lock_004_glb_mutexA_unlock () {}
void dead_lock_004_glb_mutexB_lock () {}
void dead_lock_004_glb_mutexB_unlock () {}
void dead_lock_004_glb_mutexC_lock () {}
void dead_lock_004_glb_mutexC_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int dead_lock_004_glb_dataA = 0;
int dead_lock_004_glb_dataB = 0;
int dead_lock_004_glb_dataC = 0;

void* dead_lock_004_tsk_001 (void *pram)
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataA = (dead_lock_004_glb_dataA % 100) + 1;

	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataB = (dead_lock_004_glb_dataB % 100) + 1;

	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataC = (dead_lock_004_glb_dataC % 100) + 1;
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_004_tsk_002 (void *pram)
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexB); /*Tool should detect this line as error*/ /*ERROR:Dead Lock*/
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataB = (dead_lock_004_glb_dataB % 100) + 1;

	/* lock C */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataC = (dead_lock_004_glb_dataC % 100) + 1;

	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_004_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_004_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_004_glb_dataA = (dead_lock_004_glb_dataA % 100) + 1;

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexC);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexC_);
#endif /* ! defined(CHECKER_POLYSPACE) */


#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_004_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_004_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void dead_lock_004 ()
{
	pthread_t tid1;
	pthread_t tid2;

	pthread_mutex_init(dead_lock_004_glb_mutexA, NULL);
	pthread_mutex_init(dead_lock_004_glb_mutexB, NULL);
	pthread_mutex_init(dead_lock_004_glb_mutexC, NULL);

	pthread_create(&tid1, NULL, dead_lock_004_tsk_001, NULL);
	pthread_create(&tid2, NULL, dead_lock_004_tsk_002, NULL);

	pthread_join(tid1, NULL);
	pthread_join(tid2, NULL);

	pthread_mutex_destroy(dead_lock_004_glb_mutexA);
	pthread_mutex_destroy(dead_lock_004_glb_mutexB);
	pthread_mutex_destroy(dead_lock_004_glb_mutexC);
}

#if defined(CHECKER_POLYSPACE)
void dead_lock_004_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_004_tsk_001(NULL);
		}
	}
}

void dead_lock_004_tskentry_002 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_004_tsk_002(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Complexity: exclusive control over resources, across functions
 */
pthread_mutex_t dead_lock_005_glb_mutexA_;
pthread_mutex_t dead_lock_005_glb_mutexB_;
pthread_mutex_t *dead_lock_005_glb_mutexA = &dead_lock_005_glb_mutexA_;
pthread_mutex_t *dead_lock_005_glb_mutexB = &dead_lock_005_glb_mutexB_;
#if defined(CHECKER_POLYSPACE)
void dead_lock_005_glb_mutexA_lock () {}
void dead_lock_005_glb_mutexA_unlock () {}
void dead_lock_005_glb_mutexB_lock () {}
void dead_lock_005_glb_mutexB_unlock () {}
#endif /* #if defined(CHECKER_POLYSPACE) */

int dead_lock_005_glb_dataA = 0;
int dead_lock_005_glb_dataB = 0;

void dead_lock_005_func_001 ()
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_005_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_005_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */

	dead_lock_005_glb_dataB = (dead_lock_005_glb_dataB % 100) + 1;

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_005_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_005_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
}

void dead_lock_005_func_002 ()
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_005_glb_mutexA);/*Tool should detect this line as error*/ /*ERROR:Dead Lock*/
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_005_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */

	dead_lock_005_glb_dataA = (dead_lock_005_glb_dataA % 100) + 1;

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_005_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_005_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
}

void* dead_lock_005_tsk_001 (void *pram)
{
	/* lock A */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_005_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_005_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_005_glb_dataA = (dead_lock_005_glb_dataA % 100) + 1;

	/* lock B */
	dead_lock_005_func_001();

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_005_glb_mutexA);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_005_glb_mutexA_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void* dead_lock_005_tsk_002 (void *pram)
{
	/* lock B */
#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_lock(dead_lock_005_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_lock(&dead_lock_005_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	dead_lock_005_glb_dataB = (dead_lock_005_glb_dataB % 100) + 1;

	/* lock A */
	dead_lock_005_func_002();

#if ! defined(CHECKER_POLYSPACE)
	pthread_mutex_unlock(dead_lock_005_glb_mutexB);
#else /* ! defined(CHECKER_POLYSPACE) */
	pthread_mutex_unlock(&dead_lock_005_glb_mutexB_);
#endif /* ! defined(CHECKER_POLYSPACE) */
	return NULL;
}

void dead_lock_005 ()
{
	printf("dead lock");
	pthread_t tid1;
	pthread_t tid2;

	pthread_mutex_init(dead_lock_005_glb_mutexA, NULL);
	pthread_mutex_init(dead_lock_005_glb_mutexB, NULL);

	pthread_create(&tid1, NULL, dead_lock_005_tsk_001, NULL);
	pthread_create(&tid2, NULL, dead_lock_005_tsk_002, NULL);

	pthread_join(tid1, NULL);
	pthread_join(tid2, NULL);

	pthread_mutex_destroy(dead_lock_005_glb_mutexA);
	pthread_mutex_destroy(dead_lock_005_glb_mutexB);
}

#if defined(CHECKER_POLYSPACE)
void dead_lock_005_tskentry_001 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_005_tsk_001(NULL);
		}
	}
}

void dead_lock_005_tskentry_002 ()
{
	while (1)
	{
		if (rand())
		{
			dead_lock_005_tsk_002(NULL);
		}
	}
}
#endif /* defined(CHECKER_POLYSPACE) */

/*
 * Types of defects: deadlock
 * Deadlock main function
 */
extern volatile int vflag;
void dead_lock_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		dead_lock_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		dead_lock_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		dead_lock_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		dead_lock_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		dead_lock_005();
	}
}
