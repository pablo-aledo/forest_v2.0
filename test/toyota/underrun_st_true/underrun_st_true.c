/********Software Analysis - FY2013*************/
/*
* File Name: underrun_st.c
* Defect Classification
* ---------------------
* Defect Type: Static memory defects
* Defect Sub-type: Static buffer underrun
* Description: Defect Free Code to identify false positives in stack underun condition
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
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1-dimensional array	int	Constant	Loading
 */
void underrun_st_001 ()
{
	int buf[5] = {1, 2, 3, 4, 5};
	int ret;
	ret = buf[0]; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
        sink = ret;
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1-dimensional array	int	Constant	Write
 */
void underrun_st_002 ()
{
	int buf[5];
	buf[0] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
        sink = buf[idx];
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1-dimensional array	int	Variable	Write
 */
void underrun_st_003 ()
{
	int buf[5];
	int index = 0;
	buf[index] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
        sink = buf[idx];
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 single pointer	int	Alias for Subtraction	Constant-1	Loading
 */
void underrun_st_004 ()
{
	int buf[5] = {1, 2, 3, 4, 5};
	int *p;
	int ret;
	p = &buf[1];
	ret = *(p - 1); /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
        sink = ret;
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 single pointer	int	Alias for Subtraction	Constant -1	Write
 */
void underrun_st_005 ()
{
	int buf[5];
	int *p;
	p = &buf[1];
	*(p - 1) = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 single pointer	int	Alias for Subtraction	1 Variable	Write
 */
void underrun_st_006 ()
{
	int buf[5];
	int *p;
	int index = 1;
	p = &buf[1];
	*(p - index) = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 loop	1-Dimensional array
 */
void underrun_st_007 ()
{
	int buf[5];
	int i;
	for (i = 4; i > -1; i --)
	{
		buf[i] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
	}
        sink = buf[idx];
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: a decrement in a loop pointer value
 */
void underrun_st_008 ()
{
	int buf[5];
	int *p;
	int i;
	p = &buf[4];
	for (i = 0; i < 5; i ++)
	{
		*p = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
		p --;
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 loop	1-Dimensional array
 */
int underrun_st_009_gbl_buf[5];
void underrun_st_009 ()
{
	int i;
	for (i = 4; i > -1; i --)
	{
		underrun_st_009_gbl_buf[i] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: a decrement in a loop pointer value
 */
int underrun_st_010_gbl_buf[5];
void underrun_st_010 ()
{
	int *p;
	int i;
	p = &underrun_st_010_gbl_buf[4];
	for (i = 0; i < 5; i ++)
	{
		*p = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
		p --;
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 loop	1-Dimensional array
 */
int underrun_st_011_gbl_buf[5];
void underrun_st_011 ()
{
	int i=4;
	while(i > -1)
	{
		underrun_st_011_gbl_buf[i] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
	    i--;
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: a decrement in a loop pointer value
 */
int underrun_st_012_gbl_buf[5];
void underrun_st_012 ()
{
	int *p;
	p = &underrun_st_012_gbl_buf[4];
	int i=4;
	while(i > -1)
	{
		*p = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
		p --;
		i--;
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * Complexity: 1 loop	1-Dimensional array
 */
int underrun_st_013_gbl_buf[5];
void underrun_st_013 ()
{
	int i=4;
	int var=0;
	while(i > -1)
	{
		if(var==0)
		underrun_st_013_gbl_buf[i] = 1; /*Tool should not detect this line as error*/ /*No ERROR:Data Underrun*/
	    i--;
	}
}

/*
 * Types of defects: buffer underrun ( static buffer )
 * buffer underrun ( static buffer ) - Main function
 */
extern volatile int vflag;
void underrun_st_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		underrun_st_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		underrun_st_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		underrun_st_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		underrun_st_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		underrun_st_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		underrun_st_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		underrun_st_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		underrun_st_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		underrun_st_009();
	}

	if (vflag == 10 || vflag ==888)
	{
		underrun_st_010();
	}

	if (vflag == 11 || vflag ==888)
	{
		underrun_st_011();
	}

	if (vflag == 12 || vflag ==888)
	{
		underrun_st_012();
	}

	if (vflag == 13 || vflag ==888)
	{
		underrun_st_013();
	}
}
