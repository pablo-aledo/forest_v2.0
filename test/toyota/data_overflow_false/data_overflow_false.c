/********Software Analysis - FY2013*************/
/*
* File Name: data_overflow.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Data overflow
* Description: Defect Code to identify defects in data overflow in static declaration
*/

static int sink;

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
 * Types of defects: overflow
 * Complexity: Overflow in char + 1	Constant
 */
void data_overflow_001 ()
{
	char max = 0x7f;
	char ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in short + 1	Constant
 */
void data_overflow_002 ()
{
	short max = 0x7fff;
	short ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in int + 1	Constant
 */
void data_overflow_003 ()
{
	int max = 0x7fffffff;
	int ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in long + 1	Constant
 */
void data_overflow_004 ()
{
	long max = 0x7fffffff;
	long ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in unsigned char  + 1	Constant
 */
void data_overflow_005 ()
{
	unsigned char max = 0xff;
	unsigned char ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in unsigned short  + 1	Constant
 */
void data_overflow_006 ()
{
	unsigned short max = 0xffff;
	unsigned short ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in unsigned int  + 1	Constant
 */
void data_overflow_007 ()
{
	unsigned int max = 0xffffffff;
	unsigned int ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: Overflow in unsigned long  + 1	Constant
 */
void data_overflow_008 ()
{
	unsigned long max = 0xffffffff;
	unsigned long ret;
	ret = max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: overflow in constant (signed) +1 bit field
 */
typedef struct {
	signed int max : 5;
	signed int ret : 5;
} data_overflow_009_s_001;

void data_overflow_009 ()
{
	data_overflow_009_s_001 s;
	s.max = 0x0f;
	s.ret = s.max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
}

/*
 * Types of defects: overflow
 * Complexity: overflow in constant (unsigned) +1 bit field
 */
typedef struct {
	unsigned int max : 5;
	unsigned int ret : 5;
} data_overflow_010_s_001;

void data_overflow_010 ()
{
	data_overflow_010_s_001 s;
	s.max = 0x1f;
	s.ret = s.max + 1;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
}

/*
 * Types of defects: overflow
 * Complexity: int	Increment ++ operator
 */
void data_overflow_011 ()
{
	int max = 0x7fffffff;
	int ret;
	max ++;
	ret = max;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow + 128	Constant
 */
void data_overflow_012 ()
{
	int max = 0x7fffff80;
	int ret;
	ret = max + 128;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	That overflow in multiplication	Constant
 */
void data_overflow_013 ()
{
	int max = 0x40000000;
	int ret;
	ret = max * 2;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at + 1	Variable
 */
void data_overflow_014 ()
{
	int max = 0x7fffffff;
	int d = 1;
	int ret;
	ret = max + d;/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Value of random variable + 1
 */
void data_overflow_015 ()
{
	int max = 0x7fffffff;
	int d;
	int ret;
	d = rand();
	ret = max + d; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Linear equation
 */
void data_overflow_016 ()
{
	int max = 429496729;
	int ret;
	ret = (5 * max) + 3; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Nonlinear equation
 */
void data_overflow_017 ()
{
	int max = 46340;
	int ret;
	ret = (max * max) + 88048; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at The return value of the function
 */
int data_overflow_018_func_001 ()
{
	return 1;
}

void data_overflow_018 ()
{
	int max = 0x7fffffff;
	int ret;
	ret = max + data_overflow_018_func_001(); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Function arguments
 */
void data_overflow_019_func_001 (int d)
{
	int max = 0x7fffffff;
	int ret;
	ret = max + d; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

void data_overflow_019 ()
{
	data_overflow_019_func_001(1);
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at	An array of element values
 */
void data_overflow_020 ()
{
	int max = 0x7fffffff;
	int dlist[4] = {0, 1, -2, -1};
	int ret;
	ret = max + dlist[1]; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Alias for 1 weight
 */
void data_overflow_021 ()
{
	int max = 0x7fffffff;
	int d = 1;
	int d1;
	int ret;
	d1 = d;
	ret = max + d1; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: int	Overflow at Also known as double
 */
void data_overflow_022 ()
{
	int max = 0x7fffffff;
	int d = 1;
	int d1;
	int d2;
	int ret;
	d1 = d;
	d2 = d1;
	ret = max + d2; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: the operands is a constant
 */
void data_overflow_023 ()
{
	int ret;
	ret = 0x7fffffff + 1; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: floating point overflow (double)
 */
void data_overflow_024 ()
{
	float ret;

	/* 0 11111110 11111111111111111111111 */
	float max = 3.40282347e+38F;

	/* 0 11100111 00000000000000000000000 */
	ret = max + 2.02824096e+31F; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 * Types of defects: overflow
 * Complexity: floating point overflow (double)
 */
void data_overflow_025 ()
{
	double ret;

	/* 0 11111111110 1111111111111111111111111111111111111111111111111111 */
	double max = 1.7976931348623157e+308;

	/* 0 11111001010 0000000000000000000000000000000000000000000000000000 */
	ret = max + 1.9958403095347198e+292; /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        sink = ret;
}

/*
 *
 */
extern volatile int vflag;
void data_overflow_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		data_overflow_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		data_overflow_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		data_overflow_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		data_overflow_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		data_overflow_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		data_overflow_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		data_overflow_007();
	}

	if (vflag ==8 || vflag ==888)
	{
		data_overflow_008();
	}

	if (vflag ==9 || vflag ==888)
	{
		data_overflow_009();
	}

	if (vflag ==10 || vflag ==888)
	{
		data_overflow_010();
	}

	if (vflag ==11 || vflag ==888)
	{
		data_overflow_011();
	}

	if (vflag ==12 || vflag ==888)
	{
		data_overflow_012();
	}

	if (vflag ==13 || vflag ==888)
	{
		data_overflow_013();
	}

	if (vflag ==14 || vflag ==888)
	{
		data_overflow_014();
	}

	if (vflag ==15 || vflag ==888)
	{
		data_overflow_015();
	}

	if (vflag ==16 || vflag ==888)
	{
		data_overflow_016();
	}

	if (vflag ==17 || vflag ==888)
	{
		data_overflow_017();
	}

	if (vflag ==18 || vflag ==888)
	{
		data_overflow_018();
	}

	if (vflag ==19 || vflag ==888)
	{
		data_overflow_019();
	}

	if (vflag ==20 || vflag ==888)
	{
		data_overflow_020();
	}

	if (vflag ==21 || vflag ==888)
	{
		data_overflow_021();
	}

	if (vflag ==22 || vflag ==888)
	{
		data_overflow_022();
	}

	if (vflag ==23 || vflag ==888)
	{
		data_overflow_023();
	}

	if (vflag ==24 || vflag ==888)
	{
		data_overflow_024();
	}

	if (vflag ==25 || vflag ==888)
	{
		data_overflow_025();
	}
}
