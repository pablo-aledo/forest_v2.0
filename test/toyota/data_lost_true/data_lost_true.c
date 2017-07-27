/********Software Analysis - FY2013*************/
/*
* File Name: data_lost.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Integer precision lost because of cast
* Description: Defect Free Code to identify false positives in data lost at cast
*/

static int sink;

int rand (void);
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
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: char	-> short	Variable
 */
void data_lost_001 ()
{
	char ret;
	short a = 0x7f;
	ret = a; /*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: short-> int	Variable
 */
void data_lost_002 ()
{
	short ret;
	int a = 0x7fff;
	ret = a; /*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	long	Variable
 */
void data_lost_003 ()
{
	short ret;
	long a = 0x7fff;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: int	float	Variable
 */
void data_lost_004 ()
{
	int ret;
	float a = 2.14748352e+09F; /* 0x7fffff80 */
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a long	float	Variable
 */
void data_lost_005 ()
{
	long ret;
	float a = 2.14748352e+09F; /* 0x7fffff80 */
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: float	double	Variable
 */
void data_lost_006 ()
{
	float ret;	/* MAX:2^127 * (2 - 2^(-23)) */
	double a = 3.4028232635611926e+38;	/* 2^127 * (2 - 2^(-23)) */
        // JDR: next line is a lossy cast!
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: unsigned char	unsigned short	Variable
 */
void data_lost_007 ()
{
	unsigned char ret;
	unsigned short a = 0xff;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: unsigned short	unsigned int	Variable
 */
void data_lost_008 ()
{
	unsigned short ret;
	unsigned int a = 0xffff;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: unsigned short	unsigned long	Variable
 */
void data_lost_009 ()
{
	unsigned short ret;
	unsigned long a = 0xffff;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: ( signed) bitfield	( signed) bit field	Variable
 */
typedef struct {
	signed int ret : 5;
	signed int a : 7;
} data_lost_010_s_001;

void data_lost_010 ()
{
	data_lost_010_s_001 s;
	s.a = 0x0f;
	s.ret = s.a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Constant
 */
void data_lost_011 ()
{
	short ret;
	ret = 0x7fff;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Value of random variable
 */
void data_lost_012 ()
{
	short ret;
	int a;
	a = rand() % 0x8000;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Linear equation
 */
void data_lost_013 ()
{
	short ret;
	int a = 129;
	ret = (254 * a) + 1;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Nonlinear equation
 */
void data_lost_014 ()
{
	short ret;
	int a = 181;
	ret = (a * a) + 6;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	The return value of the function
 */
int data_lost_015_func_001 ()
{
	return 0x7fff;
}

void data_lost_015 ()
{
	short ret;
	ret = data_lost_015_func_001();/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Function arguments
 */
void data_lost_016_func_001 (int a)
{
	short ret;
	ret = a;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

void data_lost_016 ()
{
	data_lost_016_func_001(0x7fff);
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	An array of element values
 */
void data_lost_017 ()
{
	short ret;
	int buf[5] = {0x8111, 0x8001, 0x8011, 0x7fff, 0x8111};
	ret = buf[3];/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	Alias for 1 weight
 */
void data_lost_018 ()
{
	short ret;
	int a = 0x7fff;
	int a1;
	a1 = a;
	ret = a1;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * Complexity: a short	int	- double alias
 */
void data_lost_019 ()
{
	short ret;
	int a = 0x7fff;
	int a1;
	int a2;
	a1 = a;
	a2 = a1;
	ret = a2;/*Tool should Not detect this line as error*/ /*No ERROR:Integer precision lost because of cast*/
        sink = ret;
}

/*
 * Types of defects: assignment from large to small size data type - data lost  problem
 * data lost main function
 */
extern volatile int vflag;
void data_lost_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		data_lost_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		data_lost_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		data_lost_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		data_lost_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		data_lost_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		data_lost_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		data_lost_007();
	}

	if (vflag ==8 || vflag ==888)
	{
		data_lost_008();
	}

	if (vflag ==9 || vflag ==888)
	{
		data_lost_009();
	}

	if (vflag ==10 || vflag ==888)
	{
		data_lost_010();
	}

	if (vflag ==11 || vflag ==888)
	{
		data_lost_011();
	}

	if (vflag ==12 || vflag ==888)
	{
		data_lost_012();
	}

	if (vflag ==13 || vflag ==888)
	{
		data_lost_013();
	}

	if (vflag ==14 || vflag ==888)
	{
		data_lost_014();
	}

	if (vflag ==15 || vflag ==888)
	{
		data_lost_015();
	}

	if (vflag ==16 || vflag ==888)
	{
		data_lost_016();
	}

	if (vflag ==17 || vflag ==888)
	{
		data_lost_017();
	}

	if (vflag ==18 || vflag ==888)
	{
		data_lost_018();
	}

	if (vflag ==19 || vflag ==888)
	{
		data_lost_019();
	}
}
