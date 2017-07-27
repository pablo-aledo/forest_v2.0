/********Software Analysis - FY2013*************/
/*
* File Name: double_release.c
* Defect Classification
* ---------------------
* Defect Type: Concurrency defects
* Defect Sub-type: Double release
* Description: Defect Free Code to identify false positives in double release - concurrency defects
*/

/*You can specify the-lpthread to include <pthread.h>  Compile options */

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

int rand (void);

/*
* Types of defects: double release
* Complexity: double release
*/
pthread_mutex_t double_release_001_glb_mutex_;
pthread_mutex_t * double_release_001_glb_mutex = & double_release_001_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_001_glb_mutex_lock () {}
void double_release_001_glb_mutex_unlock () {}
/* # Endif  # if defined (CHECKER_POLYSPACE) */

int double_release_001_glb_data = 0;

void * double_release_001_tsk_001 (void * pram)
{
	pthread_mutex_lock (double_release_001_glb_mutex);
    double_release_001_glb_data = (double_release_001_glb_data% 100) + 1;
    pthread_mutex_unlock (double_release_001_glb_mutex); /*Tool should not detect this line as error*/ /*No ERROR:Double UnLock*/
    return NULL;
}

void double_release_001 ()
{
	pthread_t tid1;
    pthread_mutex_init (double_release_001_glb_mutex, NULL);
    pthread_create (& tid1, NULL, double_release_001_tsk_001, NULL);
    pthread_join (tid1, NULL);
    pthread_mutex_destroy (double_release_001_glb_mutex);
}

/* # If defined (CHECKER_POLYSPACE) */
void double_release_001_tskentry_001 ()
{
	while (1)
   {
		if (rand ())
        {
			double_release_001_tsk_001 (NULL);
        }
    }
}
/* # Endif  defined (CHECKER_POLYSPACE) */

/*
* Types of defects: double release
* Complexity:Unlock without locking
*/

pthread_mutex_t double_release_002_glb_mutex_;
pthread_mutex_t * double_release_002_glb_mutex = &double_release_002_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_002_glb_mutex_lock () {}
void double_release_002_glb_mutex_unlock () {}
/* # Endif # if defined (CHECKER_POLYSPACE) */

int double_release_002_glb_data = 0;

void * double_release_002_tsk_001 (void * pram)
{
	pthread_mutex_lock (double_release_002_glb_mutex);
	double_release_002_glb_data = (double_release_002_glb_data% 100) + 1;
	pthread_mutex_unlock (double_release_002_glb_mutex);
	return NULL;
}

void * double_release_002_tsk_002 (void * pram)
{
	pthread_mutex_lock (double_release_002_glb_mutex);
	double_release_002_glb_data = (double_release_002_glb_data% 100) + 1;
	pthread_mutex_unlock (double_release_002_glb_mutex);
	return NULL;
}

void double_release_002 ()
{
	pthread_t tid1,tid2;
    pthread_mutex_init (double_release_002_glb_mutex, NULL);
    pthread_create (& tid1, NULL, double_release_002_tsk_001, NULL);
    pthread_create (& tid2, NULL, double_release_002_tsk_002, NULL);
    pthread_join (tid1, NULL);
    pthread_join (tid2, NULL);
    pthread_mutex_destroy (double_release_002_glb_mutex);
}
/* # if defined (CHECKER_POLYSPACE) */
void double_release_002_tskentry_001 ()
{
	while (1)
    {
		if (rand ())
		{
			double_release_002_tsk_001 (NULL);
		}
    }
}
/* # endif  defined (CHECKER_POLYSPACE) */

/*
* Types of defects: double Release
* Complexity: double release across function 
*/
pthread_mutex_t double_release_003_glb_mutex_;
pthread_mutex_t * double_release_003_glb_mutex = & double_release_003_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_003_glb_mutex_lock () {}
void double_release_003_glb_mutex_unlock () {}
/* # Endif  # if defined (CHECKER_POLYSPACE) */

int double_release_003_glb_data = 0;

void double_release_003_func_001 ()
{
	pthread_mutex_unlock (double_release_003_glb_mutex);
}

void * double_release_003_tsk_001 (void * pram)
{
	pthread_mutex_lock (double_release_003_glb_mutex);
	double_release_003_glb_data = (double_release_003_glb_data% 100) + 1;
	double_release_003_func_001 (); /*Tool should not detect this line as error*/ /*No ERROR:Double UnLock*/
	return NULL;
}

void double_release_003 ()
{
	pthread_t tid1;
	pthread_mutex_init (double_release_003_glb_mutex, NULL);
	pthread_create (& tid1, NULL, double_release_003_tsk_001, NULL);
	pthread_join (tid1, NULL);
	pthread_mutex_destroy (double_release_003_glb_mutex);
}

/* # If defined (CHECKER_POLYSPACE) */
void double_release_003_tskentry_001 ()
{
	while (1)
	{
		if (rand ())
		{
			double_release_003_tsk_001 (NULL);
		}
	}
}
/* # Endif defined (CHECKER_POLYSPACE) */

/*
* Types of defects: double Release
* Complexity: double release inside and outside a loop
*/
pthread_mutex_t double_release_004_glb_mutex_;
pthread_mutex_t * double_release_004_glb_mutex = & double_release_004_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_004_glb_mutex_lock () {}
void double_release_004_glb_mutex_unlock () {}
/* # Endif # if defined (CHECKER_POLYSPACE) */

int double_release_004_glb_data = 0;

void * double_release_004_tsk_001 (void * pram)
{
	int i;
	for(i=0;i<2;i++)
	{
		pthread_mutex_lock (double_release_004_glb_mutex);
		double_release_004_glb_data = (double_release_004_glb_data% 100) + 1;
		pthread_mutex_unlock (double_release_004_glb_mutex); /*Tool should not detect this line as error*/ /*No ERROR:Double UnLock*/
	}
    return NULL;
}

void double_release_004 ()
{
	pthread_t tid1;
    pthread_mutex_init (double_release_004_glb_mutex, NULL);
    pthread_create (& tid1, NULL, double_release_004_tsk_001, NULL);
    pthread_join (tid1, NULL);
    pthread_mutex_destroy (double_release_004_glb_mutex);
}

/* # If defined (CHECKER_POLYSPACE) */
void double_release_004_tskentry_001 ()
{
	while (1)
	{
		if (rand ())
		{
			double_release_004_tsk_001 (NULL);
		}
	}
}
/* # Endif defined (CHECKER_POLYSPACE) */



/*
* Types of defects: double Release
* Complexity: double release inside a loop
*/
pthread_mutex_t double_release_005_glb_mutex_;
pthread_mutex_t * double_release_005_glb_mutex = & double_release_005_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_005_glb_mutex_lock () {}
void double_release_005_glb_mutex_unlock () {}
/* # Endif / * # if defined (CHECKER_POLYSPACE) */

int double_release_005_glb_data = 0;

void * double_release_005_tsk_001 (void * pram)
{
	int i;
	pthread_mutex_lock (double_release_005_glb_mutex);
	double_release_005_glb_data = (double_release_005_glb_data% 100) + 1;
	for(i=0;i<1;i++)
	{
		pthread_mutex_unlock (double_release_005_glb_mutex);  /*Tool should not detect this line as error*/ /*No ERROR:Double UnLock*/
	}
	return NULL;
}

void double_release_005 ()
{
	pthread_t tid1;
    pthread_mutex_init (double_release_005_glb_mutex, NULL);
    pthread_create (& tid1, NULL, double_release_005_tsk_001, NULL);
    pthread_join (tid1, NULL);
    pthread_mutex_destroy (double_release_005_glb_mutex);
}

/* # If defined (CHECKER_POLYSPACE) */
void double_release_005_tskentry_001 ()
{
	while (1)
	{
		if (rand ())
		{
			double_release_005_tsk_001 (NULL);
		}
	}
}
/* # Endif defined (CHECKER_POLYSPACE) */
/*
* Types of defects: double Release
* Complexity: Second release in if condition
*/
pthread_mutex_t double_release_006_glb_mutex_;
pthread_mutex_t * double_release_006_glb_mutex = & double_release_006_glb_mutex_;
/* # If defined (CHECKER_POLYSPACE) */
void double_release_006_glb_mutex_lock () {}
void double_release_006_glb_mutex_unlock () {}
/* # Endif # if defined (CHECKER_POLYSPACE) */

int double_release_006_glb_data = 0;

void * double_release_006_tsk_001 (void * pram)
{
	pthread_mutex_lock (double_release_006_glb_mutex);
	double_release_006_glb_data = (double_release_006_glb_data% 100) + 1;
	pthread_mutex_unlock (double_release_006_glb_mutex);/*Tool should not detect this line as error*/ /*No ERROR:Double UnLock*/
	return NULL;
}

void double_release_006 ()
{
	pthread_t tid1;
    pthread_mutex_init (double_release_006_glb_mutex, NULL);
    pthread_create (& tid1, NULL, double_release_006_tsk_001, NULL);
    pthread_join (tid1, NULL);
    pthread_mutex_destroy (double_release_006_glb_mutex);
}

/* # If defined (CHECKER_POLYSPACE) */
void double_release_006_tskentry_001 ()
{
	while (1)
	{
		if (rand ())
		{
			double_release_006_tsk_001 (NULL);
		}
	}
}
/* # Endif defined (CHECKER_POLYSPACE) */
/*
*
*/
extern volatile int vflag;
void double_release_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		double_release_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		double_release_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		double_release_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		double_release_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		double_release_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		double_release_006();
	}
}
