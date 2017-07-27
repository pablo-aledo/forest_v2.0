/********Software Analysis - FY2013*************/
/*
* File Name: not_return.c
* Defect Classification
* ---------------------
* Defect Type: Misc defects
* Defect Sub-type: Non void function does not return value
* Description: Defect Free Code to identify false positives in conditions like having return value
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
int rand (void);

/*
 * Type of defect: there is a path that does not return a return value
 * Complexity: if it contains if statements
 */
int not_return_001_func_001 (int flag)
{
	if (flag == 0)
	{
		return 0;
	}
	else
	{
		return 1;  /*Tool should not detect this line as error*/ /*No ERROR: No return value */
	}
}

void not_return_001 ()
{
	int ret;
	ret = not_return_001_func_001(rand());
        sink = ret;
}

/*
 * Type of defect: there is a path that does not return a return value
 * Complexity: if it contains nested if statements
 */
int not_return_002_func_001 (int flag1, int flag2)
{
	if (flag1 == 0)
	{
		if (flag2 == 0)
		{
			return 0;
		}
		return 1;  /*Tool should not detect this line as error*/ /*No ERROR: No return value */
	}
	else
	{
		return 0;
	}
}

void not_return_002 ()
{
	int ret;
	ret = not_return_002_func_001(rand(), rand());
        sink = ret;
}

/*
 * Type of defect: there is a path that does not return a return value
 * Complexity: if it contains a switch
 */
int not_return_003_func_001 (int flag)
{
	switch (flag)
	{
		case 1:
			return 0;
		case 2:
			return 1;
		case 3:
			return 0;
		default:
			return -1;
	}
}  /*Tool should not detect this line as error*/ /*No ERROR: No return value */

void not_return_003 ()
{
	int ret;
	ret = not_return_003_func_001(rand());
        sink = ret;
}

/*
 * Type of defect: there is a path that does not return a return value
 * Complexity: if it contains the goto
 */
int not_return_004_func_001 (int flag)
{
	int ret = 0;
	if (flag == 0)
	{
		goto my_label;
	}
	return ret;
my_label:
	ret ++;
	return ret;
}  /*Tool should not detect this line as error*/ /*No ERROR: No return value */

void not_return_004 ()
{
	int ret;
	ret = not_return_004_func_001(rand());
        sink = ret;
}

/*
 * Type of defect: there is a path that does not return a return value
 *Complexity: Not return main function
 */
extern volatile int vflag;
void not_return_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		not_return_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		not_return_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		not_return_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		not_return_004();
	}
}
