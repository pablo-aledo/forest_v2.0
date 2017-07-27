/********Software Analysis - FY2013*************/
/*
* File Name: double_free.c
* Defect Classification
* ---------------------
* Defect Type: Resource management defects
* Defect Sub-type: Double free
* Description: Defect Free Code to identify false positives in double free - resource management defects
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
* Types of defects: Double free
* Complexity: Basic type where pointer is "freed"  twice
*/

void double_free_001()
{
	char* ptr= (char*) malloc(sizeof(char));

	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Basic type where pointer is "freed" in a if condition in a loop
*/

void double_free_002()
{
	char* ptr= (char*) malloc(10*sizeof(char));
	int i;
	
	for(i=0;i<10;i++)
	{
		ptr[i]='a';
		if(i==10)
		free(ptr);
	}
	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Basic type where pointer is "freed" in a loop and then outside the loop
*/

void double_free_003()
{
	char* ptr= (char*) malloc(10*sizeof(char));
	int i;
	
	for(i=0;i<10;i++)
	{
		*(ptr+i)='a';
		
	}

	free(ptr);  /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Memory is free in a if statement
*/

void double_free_004()
{
	char* ptr= (char*) malloc(10*sizeof(char));
	int i;
	for(i=0;i<10;i++)
	{
		*(ptr+i)='a';

	}
	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Memory is free in a if statement
*/

void double_free_005()
{
	char* ptr= (char*) malloc(sizeof(char));

	if(ptr)
	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Memory is free in a constant if statement
*/

void double_free_006()
{
	char* ptr= (char*) malloc(sizeof(char));
	if(0)
	free(ptr);

	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity: Memory is free in a variable if statement
*/

void double_free_007()
{
	char* ptr= (char*) malloc(sizeof(char));
	int flag=0;
	
	if(flag<0)
	free(ptr);

	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity:Free in a function
*/
char *double_free_function_008_gbl_ptr;
void double_free_function_008()
{
	free (double_free_function_008_gbl_ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

void double_free_008()
{
	double_free_function_008_gbl_ptr= (char*) malloc(sizeof(char));

	double_free_function_008();
}

/*
* Types of defects: Double free
* Complexity:Free in a while loop with a variable
*/


void double_free_009()
{
	char* ptr= (char*) malloc(sizeof(char));
	int flag=0;

	while(flag==1)
	{
		free(ptr);
		flag++;
	}
	free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
}

/*
* Types of defects: Double free
* Complexity:Free in a while loop with a constant
*/


void double_free_010()
{
	char* ptr= (char*) malloc(sizeof(char));
	int flag=1;

	while(flag)
	{
		free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
		flag--;
	}
}

/*
* Types of defects: Double free
* Complexity:double Free in a while loop with a condition
*/


void double_free_011()
{
	char* ptr= (char*) malloc(sizeof(char));
	int flag=1,a=0,b=1;

	while(a<b)
	{
		if(flag ==1)
		free(ptr);  /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
		a++;
	}
}

/*
* Types of defects: Double free
* Complexity:double Free in a for loop
*/


void double_free_012()
{
	char* ptr= (char*) malloc(sizeof(char));
	int a=0;

	for(a=0;a<1;a++)
	{
		free(ptr); /*Tool should Not detect this line as error*/ /*No ERROR:Double free*/
	}
}

/*
* Types of defects: Double free
* double free main function
*/
extern volatile int vflag;
void double_free_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		double_free_001 ();
	}

    if (vflag == 2 || vflag ==888)
    {
    	double_free_002 ();
    }

    if (vflag == 3 || vflag ==888)
    {
    	double_free_003 ();
    }

    if (vflag == 4 || vflag ==888)
    {
    	double_free_004 ();
    }

    if (vflag == 5 || vflag ==888)
    {
    	double_free_005 ();
    }

    if (vflag == 6 || vflag ==888)
    {
    	double_free_006 ();
    }

    if (vflag == 7 || vflag ==888)
    {
    	double_free_007 ();
    }

    if (vflag == 8 || vflag ==888)
    {
    	double_free_008 ();
    }

    if (vflag == 9 || vflag ==888)
    {
    	double_free_009 ();
    }

    if (vflag == 10 || vflag ==888)
    {
    	double_free_010 ();
    }

    if (vflag == 11 || vflag ==888)
    {
    	double_free_011 ();
    }

    if (vflag == 12 || vflag ==888)
    {
    	double_free_012 ();
    }

}
