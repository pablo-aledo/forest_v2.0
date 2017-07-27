/********Software Analysis - FY2013*************/
/*
* File Name: ow_memcpy.c
* Defect Classification
* ---------------------
* Defect Type: Dynamic memory defects
* Defect Sub-type: Memory copy at overlapping areas
* Description: Defect Free Code to identify false positives in memory copy at overlapping areas
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

/*
 * Types of defects: copy of the overlapped area
 * Complexity: loop in a function
 */
void ow_memcpy_001 ()
{
	int buf[5] = {1, 2, 3, 4, 5};
	int i;

	for (i = 0; i < 2; i ++)
	{
		buf[i] = buf[i+2]; /*Tool should not detect this line as error*/ /*No ERROR:copy of the overlapped area*/
	}
}

/*
 * Types of defects: copy of the overlapped area
 * Complexity: substantial memcpy function call:
 */
void ow_memcpy_002_func_001 (void *dst, const void *src, int size)
{
	unsigned char *p;
	unsigned char *q;
	int i;
	p = (unsigned char *)src;
	q = (unsigned char *)dst;
	for (i = 0; i < size; i ++)
	{
		*q = *p; /*Tool should not detect this line as error*/ /*No ERROR:copy of the overlapped area*/
		p ++;
		q ++;
	}
}

void ow_memcpy_002 ()
{
	int buf[5] = {1, 2, 3, 4, 5};
	ow_memcpy_002_func_001(&buf[2], &buf[0], (2 * sizeof(int)));
}

/*
 * Types of defects: copy of the overlapped area
 * copy of the overlapped area main function
 */
extern volatile int vflag;
void ow_memcpy_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		ow_memcpy_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		ow_memcpy_002();
	}
}
