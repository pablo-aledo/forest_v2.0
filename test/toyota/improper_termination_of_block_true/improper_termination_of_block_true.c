/********Software Analysis - FY2013*************/
/*
* File Name: improper_termination_of_block.c
* Defect Classification
* ---------------------
* Defect Type: Inappropriate code
* Defect Sub-type: Improper termination of block
* Description: Defect Free Code to identify false positives during improper termination of block
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
* Types of defects: Improper termination of block
* Complexity: Improper termination as only 1 statement after if statement is executed
*/

void improper_termination_of_block_001()
{
	int condition=0,x=0,y=0;
	
	if (condition==0) /*Tool should not detect this line as error*/ /*No ERROR:Improper termination of block*/
	{
		printf("%d",x);
	}
	printf("%d\n",y);

}

/*
* Types of defects: Improper termination of block
* Complexity: Improper termination as only 1 statement after if statement is executed
*/

void improper_termination_of_block_002()
{
	int condition=0,x=0,y=0;
	
	if (condition==0) /*Tool should not detect this line as error*/ /*No ERROR:Improper termination of block*/
	{
		printf("%d",x);
	}
	printf("%d\n",y);

}

/*
* Types of defects: Improper termination of block
* Complexity: Improper termination as the semicolon causes for not to be executed in a loop
*/

void improper_termination_of_block_003()
{
	int x,y=0;
	
	for(x=0;x<10;x++) /*Tool should not detect this line as error*/ /*No ERROR:Improper termination of block*/
	{
		printf("%d",x);
		printf("%d",y);
	}
}

/*
* Types of defects: Improper termination of block
* Complexity: Improper termination as only 1 statement after while statement is executed
*/

void improper_termination_of_block_004()
{
	int x=0,y=0;
	
	while(x<10) /*Tool should not detect this line as error*/ /*No ERROR:Improper termination of block*/
	{
		x++;	
		printf("%d",x);
		printf("%d",y);
	}
	printf("\n");
}

extern volatile int vflag;
void improper_termination_of_block_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		improper_termination_of_block_001 ();
	}

	if (vflag == 2 || vflag ==888)
	{
		improper_termination_of_block_002 ();
	}

	if (vflag == 3 || vflag ==888)
	{
		improper_termination_of_block_003 ();
	}

	if (vflag == 4 || vflag ==888)
	{
		improper_termination_of_block_004 ();
	}

}
