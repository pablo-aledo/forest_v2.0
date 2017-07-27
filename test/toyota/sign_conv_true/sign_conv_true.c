/********Software Analysis - FY2013*************/
/*
* File Name: sign_conv.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Integer sign lost because of unsigned cast
* Description: Defect Free Code to identify false positives in losing sign due to cast
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
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: char	signed <- unsigned	unsigned char	Variable
 */
void sign_conv_001 ()
{
	unsigned char a = 0x7f;
	char ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: a short	signed <- unsigned	unsigned short	Variable
 */
void sign_conv_002 ()
{
	unsigned short a = 0x7fff;
	short ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: int	signed unsigned	<- unsigned int	Variable
 */
void sign_conv_003 ()
{
	unsigned int a = 0x7fffffff;
	int ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: a long	signed <- unsigned	unsigned long	Variable
 */
void sign_conv_004 ()
{
	unsigned long a = 0x7fffffff;
	long ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned char	unsigned <- signed	char
 */
void sign_conv_005 ()
{
	char a = 0x7f;
	unsigned char ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned short	unsigned <- signed	short	Variable
 */
void sign_conv_006 ()
{
	short a = 0x7fff;
	unsigned short ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Variable
 */
void sign_conv_007 ()
{
	int a = 0x7fffffff;
	unsigned int ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned long	unsigned <- signed	long	Variable
 */
void sign_conv_008 ()
{
	long a = 0x7fffffff;
	unsigned long ret;
	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: ( signed ) bitfield	signed <- unsigned	( unsigned ) bitfields	Variable
 */
typedef struct {
	unsigned int a : 5;
	signed int ret : 5;
} sign_conv_009_s_001;

void sign_conv_009 ()
{
	sign_conv_009_s_001 s;
	s.a = 0x0f;
	s.ret = s.a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: ( unsigned ) bitfields	unsigned <- signed	( signed ) bit field	Variable
 */
typedef struct {
	signed int a : 5;
	unsigned int ret : 5;
} sign_conv_010_s_001;

void sign_conv_010 ()
{
	sign_conv_010_s_001 s;
	s.a = 0x0f;
	s.ret = s.a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Constant
 */
void sign_conv_011 ()
{
	unsigned int ret;
	ret = 0x7fffffff; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Value of random variable
 */
void sign_conv_012 ()
{
	int a;
	unsigned int ret;

	/* 0 <= rand() <= 2147483647 (RAND_MAX) */
	a = rand();

	ret = a; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Linear equation
 */
void sign_conv_013 ()
{
	int a = -1;
	unsigned int ret;
	ret = (5 * a) + 6; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Nonlinear equation
 */
void sign_conv_014 ()
{
	int a = 2;
	unsigned int ret;
	ret = (a * a) - 3; /*Tool should not detect this line as error*/ /*NO ERROR : Integer sign lost because of unsigned cast */
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	The return value of the function
 */
unsigned int sign_conv_015_gbl_ret;
int sign_conv_015_func_001 ()
{
	return 0x7fffffff;
}

void sign_conv_015 ()
{
	sign_conv_015_gbl_ret = sign_conv_015_func_001();/*Tool should not detect this line as error*/ /*NO Error Integer sign lost because of unsigned cast */
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Function arguments
 */
int sign_conv_016_gbl_ret;
void sign_conv_016_func_001 (int a)
{
	sign_conv_016_gbl_ret = a;
}

void sign_conv_016 ()
{
	sign_conv_016_func_001(0x7fffffff);
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	An array of element values
 */
int sign_conv_017_gbl_buf[5] = {1, 2, 3, -4, 5};
int sign_conv_017_gbl_ret;
void sign_conv_017 ()
{
	sign_conv_017_gbl_ret = sign_conv_017_gbl_buf[3];
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Alias for 1 weight
 */
void sign_conv_018 ()
{
	int a = 0x7fffffff;
	int a1;
	unsigned int ret;
	a1 = a;
	ret = a1;
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * Complexity: unsigned int	unsigned <- signed	int	Also known as double alias
 */
void sign_conv_019 ()
{
	int a = 0x7fffffff;
	int a1;
	int a2;
	unsigned int ret;
	a1 = a;
	a2 = a1;
	ret = a2;
        sink = ret;
}

/*
 * Defect types :signed/unsigned The issues associated with assignment
 * signed/unsigned The issues associated with assignment main function
 */
extern volatile int vflag;
void sign_conv_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		sign_conv_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		sign_conv_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		sign_conv_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		sign_conv_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		sign_conv_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		sign_conv_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		sign_conv_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		sign_conv_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		sign_conv_009();
	}

	if (vflag == 10 || vflag ==888)
	{
		sign_conv_010();
	}

	if (vflag == 11 || vflag ==888)
	{
		sign_conv_011();
	}

	if (vflag == 12 || vflag ==888)
	{
		sign_conv_012();
	}

	if (vflag == 13 || vflag ==888)
	{
		sign_conv_013();
	}

	if (vflag == 14 || vflag ==888)
	{
		sign_conv_014();
	}

	if (vflag == 15 || vflag ==888)
	{
		sign_conv_015();
	}

	if (vflag == 16 || vflag ==888)
	{
		sign_conv_016();
	}

	if (vflag == 17 || vflag ==888)
	{
		sign_conv_017();
	}

	if (vflag == 18 || vflag ==888)
	{
		sign_conv_018();
	}

	if (vflag == 19 || vflag ==888)
	{
		sign_conv_019();
	}
}
