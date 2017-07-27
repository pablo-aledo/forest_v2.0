/********Software Analysis - FY2013*************/
/*
* File Name: endless_loop.c
* Defect Classification
* ---------------------
* Defect Type: Misc defects
* Defect Sub-type: Unintentional end less loop
* Description: Defect Free Code to identify false positives in unintentional endless looping
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
 * Types of defects: infinite loop
 * Complexity: the for statement	No ongoing condition equation
 */
void endless_loop_001 ()
{
	int ret;
	int a = 0;
	int i;
	for (i = 0; ; i ++)
	{
		a ++; /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
		if (i > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: the for statement	No initialization expression for reuse
 */
void endless_loop_002 ()
{
	int ret;
	int a = 0;
	int i;
	for (i = 0; i < 10; )
	{
		a ++;
		i ++; /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	Constant
 */
void endless_loop_003 ()
{
	int ret;
	int a = 0;
	while (1)
	{
		a ++; /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	Variable
 */
void endless_loop_004 ()
{
	int ret;
	int a = 0;
	int flag = 1;
	while (flag)
	{
		a ++; /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	The return value of the function
 */
int endless_loop_005_func_001 ()
{
	return 1;
}

void endless_loop_005 ()
{
	int ret;
	int a = 0;
	while (endless_loop_005_func_001())
	{ /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
		a ++;
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	Function arguments
 */
void endless_loop_006_func_001 (int flag)
{
	int ret;
	int a = 0;
	while (flag)
	{
		a ++; /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

void endless_loop_006 ()
{
	endless_loop_006_func_001(1);
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	(a<b)
 */
void endless_loop_007 ()
{
	int ret;
	int a = 0;
	int flag = 1;
	while (flag > 0) /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
	{
		a ++;
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: while statement	(a==b)
 */
void endless_loop_008 ()
{
	int ret;
	int a = 0;
	int flag = 0;
	while (flag == 0) /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
	{
		a ++;
		if (a > 5)
		{
			break;
		}
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * Complexity: do-while statement	Constant
 */
void endless_loop_009 ()
{
	int ret;
	int a = 0;
	do
	{
		a ++;
		if (a > 5)
		{
			break;
		}
	}
	while (1); /*Tool should Not detect this line as error*/ /*No ERROR:Unintentional end less loop*/
	ret = a;
        sink = ret;
}

/*
 * Types of defects: infinite loop
 * endless loop main function
 */
extern volatile int vflag;
void endless_loop_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		endless_loop_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		endless_loop_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		endless_loop_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		endless_loop_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		endless_loop_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		endless_loop_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		endless_loop_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		endless_loop_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		endless_loop_009();
	}
}
