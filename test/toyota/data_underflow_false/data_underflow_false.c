/********Software Analysis - FY2013*************/
/*
* File Name: data_underflow.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Data underflow
* Description: Defect Code to identify defects in data underflow in static declaration
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
 * Types of defects: underflow
 * Complexity: int	Underflow with -2	Constant
 */
void data_underflow_001 ()
{
	int min = -2147483647;	/* 0x80000001 */
	int ret;
	ret = min - 2;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: unsigned int	Underflow with -1	Constant
 */
void data_underflow_002 ()
{
	unsigned int min = 0;
	unsigned int ret;
	ret = min - 1;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: int	Decrement	-
 */
void data_underflow_003 ()
{
	int min = -2147483647;	/* 0x80000001 */
	int ret;
	min --;
	min --;
	ret = min;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: int	underflow with -128 Constant
 */
void data_underflow_004 ()
{
	int min = -2147483521;
	int ret;
	ret = min - 128;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: int	Multiply by underflow	Constant
 */
void data_underflow_005 ()
{
	int min = -1073741825;	/* 0xbfffffff */
	int ret;
	ret = min * 2;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: the operands is a constant
 */
void data_underflow_006 ()
{
	int ret;
	ret = (-2147483647) - 2;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: floating point underflow ( float )
 */
void data_underflow_007 ()
{
	float ret;

	/* 0 00000000 00000000000000000000001 */
	float min = 1.40129846e-45F;

	ret = min / 2.0F;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: floating point underflow (double)
 */
void data_underflow_008 ()
{
	double ret;

	/* 0 00000000000 0000000000000000000000000000000000000000000000000001 */
	double min = 4.9406564584124654e-324;

	ret = min / 2.0;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity:  underflow (char)
 */
void data_underflow_009 ()
{
	char min = -128;	/* 0x80000002 */
	char ret;
	ret = min - 2;/*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: int	Underflow at The return value of the function
 */
int data_underflow_010_func_001 ()
{
	return 2;
}

void data_underflow_010 ()
{
	int min = -2147483647;
	int ret;
	ret = min - data_underflow_010_func_001(); /*Tool should detect this line as error*/ /*ERROR:Data Under*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Complexity: int	Underflow at Function arguments
 */
void data_underflow_011_func_001 (int d)
{
	int min = -2147483647;
	int ret;
	ret = min - d; /*Tool should detect this line as error*/ /*ERROR:Data Underflow*/
        sink = ret;
}

void data_underflow_011 ()
{
	data_underflow_011_func_001(2);
}

/*
 * Types of defects: Underflow
 * Complexity: int	underflow at	An array of element values
 */
void data_underflow_012 ()
{
	int min = -2147483647;
	int dlist[4] = {0, 1, -2, -1};
	int ret;
	ret = min - dlist[2]; /*Tool should detect this line as error*/ /*ERROR:Data underflow*/
        sink = ret;
}

/*
 * Types of defects: underflow
 * Data underflow main function
 */
extern volatile int vflag;
void data_underflow_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		data_underflow_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		data_underflow_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		data_underflow_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		data_underflow_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		data_underflow_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		data_underflow_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		data_underflow_007();
	}

	if (vflag ==8 || vflag ==888)
	{
		data_underflow_008();
	}

	if (vflag ==9 || vflag ==888)
	{
		data_underflow_009();
	}

	if (vflag ==10 || vflag ==888)
	{
		data_underflow_010();
	}

	if (vflag ==11 || vflag ==888)
	{
		data_underflow_011();
	}

	if (vflag ==12 || vflag ==888)
	{
		data_underflow_012();
	}
}
