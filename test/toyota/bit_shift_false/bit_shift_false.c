/********Software Analysis - FY2013*************/
/*
* File Name: bit_shift.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Bit shift bigger than integral type or negative
* Description: Defect Code to identify bit shift errors
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
  * Types of defects: bit shift error
  * Complexity: constant shift to the left beyond the int size
  */
void bit_shift_001 ()
{
	int a = 1;
	int ret;
	ret = a << 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: long	Beyond the size of the left shift - Constant
 */
void bit_shift_002 ()
{
	long a = 1;
	long ret;
	ret = a << 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: unsigned int	Beyond the size of the left shift -Constant
 */
void bit_shift_003 ()
{
	unsigned int a = 1;
	unsigned int ret;
	ret = a << 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: unsigned long	Beyond the size of the left shift	Constant
 */
void bit_shift_004 ()
{
	unsigned long a = 1;
	unsigned long ret;
	ret = a << 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Shift left on negative values	Constant
 */
void bit_shift_005 ()
{
	int a = 1;
	int ret;
	ret = a << -1;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the right shift	Constant
 */
void bit_shift_006 ()
{
	int a = 1;
	int ret;
	ret = a >> 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Right shifting negative values with	Constant
 */
void bit_shift_007 ()
{
	int a = 1;
	int ret;
	ret = a >> -1;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Variable
 */
void bit_shift_008 ()
{
	int a = 1;
	int shift = 32;
	int ret;
	ret = a << shift;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Value of random variable
 */
void bit_shift_009 ()
{
	int a = 1;
	int shift;
	int ret;
	shift = rand();
	ret = a << shift;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Linear equation
 */
void bit_shift_010 ()
{
	int a = 1;
	int shift = 6;
	int ret;
	ret = a << ((5 * shift) + 2);/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Nonlinear equation
 */
void bit_shift_011 ()
{
	int a = 1;
	int shift = 5;
	int ret;
	ret = a << ((shift * shift) + 7);/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	The return value of the function
 */
int bit_shift_012_func_001 ()
{
	return 32;
}

void bit_shift_012 ()
{
	int a = 1;
	int ret;
	ret = a << bit_shift_012_func_001();/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Function arguments
 */
void bit_shift_013_func_001 (int shift)
{
	int a = 1;
	int ret;
	ret = a << shift;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

void bit_shift_013 ()
{
	bit_shift_013_func_001(32);
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	An array of element values
 */
void bit_shift_014 ()
{
	int a = 1;
	int shifts[5] = {8, 40, 16, 32, 24};
	int ret;
	ret = a << shifts[3];/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Alias for 1 weight
 */
void bit_shift_015 ()
{
	int a = 1;
	int shift = 32;
	int shift1;
	int ret;
	shift1 = shift;
	ret = a << shift1;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: int	Beyond the size of the left shift	Also known as double
 */
void bit_shift_016 ()
{
	int a = 1;
	int shift = 32;
	int shift1;
	int shift2;
	int ret;
	shift1 = shift;
	shift2 = shift1;
	ret = a << shift2;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: the operands is a constant
 */
void bit_shift_017 ()
{
	int ret;
	ret = 1 << 32;/*Tool should detect this line as error*/ /*ERROR:Bit shift error*/
        sink = ret;
}

/*
 * Types of defects: BitShift errors
 * Complexity: BitShift errors Main function
 */
extern volatile int vflag;
void bit_shift_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		bit_shift_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		bit_shift_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		bit_shift_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		bit_shift_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		bit_shift_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		bit_shift_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		bit_shift_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		bit_shift_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		bit_shift_009();
	}

	if (vflag == 10 || vflag ==888)
	{
		bit_shift_010();
	}

	if (vflag == 11 || vflag ==888)
	{
		bit_shift_011();
	}

	if (vflag == 12 || vflag ==888)
	{
		bit_shift_012();
	}

	if (vflag == 13 || vflag ==888)
	{
		bit_shift_013();
	}

	if (vflag == 14 || vflag ==888)
	{
		bit_shift_014();
	}

	if (vflag == 15 || vflag ==888)
	{
		bit_shift_015();
	}

	if (vflag == 16 || vflag ==888)
	{
		bit_shift_016();
	}

	if (vflag == 17 || vflag ==888)
	{
		bit_shift_017();
	}
}
