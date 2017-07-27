/********Software Analysis - FY2013*************/
/*
* File Name: dead_code.c
* Defect Classification
* ---------------------
* Defect Type: Inappropriate code
* Defect Sub-type: Dead code
* Description: Defect Code to identify defects in dead code
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
* Types of defects: dead code
* Complexity: Constant if statement
*/
void dead_code_001 ()
{
	int a = 0;
	int ret;
	if (0)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: the if statement	Variable
 */
void dead_code_002 ()
{
	int flag = 0;
	int a = 0;
	int ret;
	if (flag)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: the if statement	The return value of the function
 */
int dead_code_003_func_001 ()
{
	return 0;
}

void dead_code_003 ()
{
	int a = 0;
	int ret;
	if (dead_code_003_func_001())
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: the if statement	Function arguments
 */
void dead_code_004_func_001 (int flag)
{
	int a = 0;
	int ret;
	if (flag)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

void dead_code_004 ()
{
	dead_code_004_func_001(0);
}

/*
* Types of defects: dead code
* Complexity: statement expression if (a <b)
*/
void dead_code_005 ()
{
	int flag = 0;
	int a = 0;
	int ret;
	if (flag > 0)
	{
		a ++; /*Tool should  detect this line as error*/ /* ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: the if statement	(a == b)
 */
void dead_code_006 ()
{
	int flag = 1;
	int a = 0;
	int ret;
	if (flag == 0)
	{
		a ++; /*Tool should  detect this line as error*/ /* ERROR:Dead Code*/
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: the for statement	Constant
 */
void dead_code_007 ()
{
	int a = 0;
	int i;
	int ret;
	for (i = 0; i>1; i ++)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

/*
* Types of defects: dead code
* Complexity: constant while statement
*/
void dead_code_008 ()
{
	int a = 0;
	int ret;
	while (0)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

/*
* Types of defects: dead code
* Complexity: variable while statement
*/
void dead_code_009 ()
{
	int flag = 0;
	int a = 0;
	int ret;
	while (flag)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

/*
* Types of defects: dead code
* Complexity: The return value of the function while statement
*/
int dead_code_010_func_001 ()
{
	return 0;
}

void dead_code_010 ()
{
	int a = 0;
	int ret;
	while (dead_code_010_func_001())
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: while statement	Function arguments
 */
void dead_code_011_func_001 (int flag)
{
	int a = 0;
	int ret;
	while (flag)
	{
		a ++;/*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

void dead_code_011 ()
{
	dead_code_011_func_001(0);
}

/*
* Types of defects: dead code
* Complexity: expression statement while (a <b)
*/
void dead_code_012 ()
{
	int flag = 0;
	int a = 0;
	int ret;
	while (flag > 0) /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
	{
		a ++;
		break;
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Complexity: while statement	(a == b)
 */
void dead_code_013 ()
{
	int flag = 1;
	int a = 0;
	int ret;
	while (flag == 0)
	{
		a ++; /*Tool should detect this line as error*/ /*ERROR:Dead Code*/
		break;
	}
	ret = a;
        sink = ret;
}

/*
 * Types of defects: dead code
 * Dead code main function
 */
extern volatile int vflag;
void dead_code_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		dead_code_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		dead_code_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		dead_code_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		dead_code_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		dead_code_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		dead_code_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		dead_code_007();
	}

	if (vflag ==8 || vflag ==888)
	{
		dead_code_008();
	}

	if (vflag ==9 || vflag ==888)
	{
		dead_code_009();
	}

	if (vflag ==10 || vflag ==888)
	{
		dead_code_010();
	}

	if (vflag ==11 || vflag ==888)
	{
		dead_code_011();
	}

	if (vflag ==12 || vflag ==888)
	{
		dead_code_012();
	}

	if (vflag ==13 || vflag ==888)
	{
		dead_code_013();
	}
}
