/********Software Analysis - FY2013*************/
/*
* File Name: zero_division.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Division by zero
* Description: Defect Code used to identify the division by zero functionality
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
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Constant
 */
void zero_division_001 ()
{
	int dividend = 1000;
	int ret;
	ret = dividend / 0;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/ =)	Basic type	int	Constant
 */
void zero_division_002 ()
{
	int dividend = 1000;
	int ret;
	dividend /= 0;/*Tool should detect this line as error*/ /* ERROR:division by zero */
	ret = dividend;
}

/*
 * Types of defects: divide by zero
 * Complexity: calculation of retained earnings (%)	Basic type	int	Constant
 */

void zero_division_003 ()
{
	int dividend = 1000;
	int ret;
	ret = dividend % 0;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}


/*
 * Types of defects: divide by zero
 * Complexity: the remainder calculation (% =)	Basic type	int	Constant
 */
int zero_division_004_dividend_gbl = 1000;
static int zero_division_004_divisor_gbl = 1;
void zero_division_004_func_001 ()
{
	zero_division_004_dividend_gbl %= zero_division_004_divisor_gbl;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}
void zero_division_004 ()
{

	zero_division_004_divisor_gbl--;
	zero_division_004_func_001 ();

}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	1-Dimensional array	int	An array of element values
 */
void zero_division_005 ()
{
	int dividend = 1000;
	int divisors[5] = {2, 1, 0, 3, 4};
	int ret;
	ret = dividend / divisors[2];/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	1 Heavy pointer	int	Variable
 */
int zero_division_006_gbl_divisor = 0;
void zero_division_006 ()
{
	int dividend = 1000;

	int *p;
	int ret;
	p = &zero_division_006_gbl_divisor;
	ret = dividend / *p;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Structure of the	int	Variable
 */
typedef struct {
	int a;
	int b;
	int divisor;
} zero_division_007_s_001;

zero_division_007_s_001 zero_division_007_s_gbl;

void zero_division_007_func_001 ()
{
	zero_division_007_s_gbl.divisor = 0;
}

void zero_division_007 ()
{
	int dividend = 1000;
	int ret;
	zero_division_007_func_001();
	ret = dividend / zero_division_007_s_gbl.divisor;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	float	Constant
 */
void zero_division_008 ()
{
	float dividend = 1000.0;
	float ret;
	ret = dividend / 0.0;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Variable
 */
void zero_division_009 ()
{
	int dividend = 1000;
	int divisor = 0;
	int ret;
	ret = dividend / divisor;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Value of random variable
 */
void zero_division_010 ()
{
	int dividend = 1000;
	int divisor;
	int ret;
	divisor = rand();
	ret = dividend / divisor;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Linear equation
 */
void zero_division_011 ()
{
	int dividend = 1000;
	int divisor = 2;
	int ret;
	ret = dividend / (2 * divisor - 4);/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Nonlinear equation
 */
void zero_division_012 ()
{
	int dividend = 1000;
	int divisor = 2;
	int ret;
	ret = dividend / (divisor * divisor - 4);/*Tool should detect this line as error*/ /* ERROR:division by zero */

}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	The return value of the function
 */
int zero_division_013_func_001 ()
{
	return 0;
}

void zero_division_013 ()
{
	int dividend = 1000;
	int ret;
	ret = dividend / zero_division_013_func_001();/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	Function arguments
 */
void zero_division_014_func_001 (int divisor)
{
	int dividend = 1000;
	int ret;
	ret = dividend / divisor;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

void zero_division_014 ()
{
	zero_division_014_func_001(0);
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	single Alias
 */
void zero_division_015 ()
{
	int dividend = 1000;
	int divisor = 0;
	int divisor1;
	int ret;
	divisor1 = divisor;
	ret = dividend / divisor1;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * Complexity: divide (/)	Basic type	int	 double alias
 */
int *zero_division_016_gbl_divisor ;
void zero_division_016_func_001 ()
{
	zero_division_016_gbl_divisor = malloc(1*sizeof(int));
	*zero_division_016_gbl_divisor= -1;
}
void zero_division_016_func_002 ()
{
	(*zero_division_016_gbl_divisor)++;
}
void zero_division_016 ()
{
	int dividend = 1000;
	int divisor1;
	int divisor2;
	int ret;
	zero_division_016_func_001 ();
	zero_division_016_func_002 ();
	divisor1 = *zero_division_016_gbl_divisor;
	divisor2 = divisor1;
	ret = dividend / divisor2;/*Tool should detect this line as error*/ /* ERROR:division by zero */
}

/*
 * Types of defects: divide by zero
 * divide by zero main function
 */
extern volatile int vflag;
void zero_division_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		zero_division_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		zero_division_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		zero_division_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		zero_division_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		zero_division_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		zero_division_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		zero_division_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		zero_division_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		zero_division_009();
	}

	if (vflag == 10 || vflag ==888)
	{
		zero_division_010();
	}

	if (vflag == 11 || vflag ==888)
	{
		zero_division_011();
	}

	if (vflag == 12 || vflag ==888)
	{
		zero_division_012();
	}

	if (vflag == 13 || vflag ==888)
	{
		zero_division_013();
	}

	if (vflag == 14 || vflag ==888)
	{
		zero_division_014();
	}

	if (vflag == 15 || vflag ==888)
	{
		zero_division_015();
	}

	if (vflag == 16 || vflag ==888)
	{
		zero_division_016();
	}
}
