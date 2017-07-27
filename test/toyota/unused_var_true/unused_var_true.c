/********Software Analysis - FY2013*************/
/*
* File Name: unused_var.c
* Defect Classification
* ---------------------
* Defect Type: Inappropriate code
* Defect Sub-type: Unused variable
* Description: Defect Free Code to identify false positives to identify the unused variable in a function
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
 * Types of defects: unused variable
 * Complexity: basic types	Internal variables
 */
void unused_var_001 ()
{
	int a = 1;
	int b = 2;
	int unuse;
	unuse = a + b;
	printf("%d",unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * Complexity: structure member	Internal variables
 */
typedef struct {
	int a;
	int b;
	int unuse;
} unused_var_002_s_001;

void unused_var_002 ()
{
	unused_var_002_s_001 s;
	s.a = 1;
	s.b = 2;
	s.unuse = s.a + s.b;
	printf("%d",s.unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * Complexity: Union Member	Internal variables
 */
typedef struct {
	int a;
	int b;
} unused_var_003_s_001;

typedef struct {
	int a;
	int b;
} unused_var_003_s_002;

typedef struct {
	int a;
	int unuse;
} unused_var_003_s_003;

typedef union {
	unused_var_003_s_001 s1;
	unused_var_003_s_002 s2;
	unused_var_003_s_003 s3;
} unused_var_003_uni_001;

void unused_var_003 ()
{
	unused_var_003_uni_001 u;


	u.s1.a = 1;
	u.s1.b = 2;
	u.s3.a = u.s2.a + u.s2.b;
	u.s3.unuse = u.s1.a;
	printf("%d",u.s3.unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * Complexity: basic types	Global variables
 */
int unused_var_004_glb_a = 1;
int unused_var_004_glb_b = 2;
int unused_var_004_glb_unuse;

void unused_var_004 ()
{
	unused_var_004_glb_unuse = unused_var_004_glb_a + unused_var_004_glb_b;
	printf("%d",unused_var_004_glb_unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * Complexity: basic types	Files in the static variable
 */
static int unused_var_005_glb_a = 1;
static int unused_var_005_glb_b = 2;
static int unused_var_005_glb_unuse;

void unused_var_005 ()
{
	unused_var_005_glb_unuse = unused_var_005_glb_a + unused_var_005_glb_b;
	printf("%d",unused_var_005_glb_unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * Complexity: basic types	Function in the static variable
 */
void unused_var_006 ()
{
	static int a = 1;
	static int b = 2;
	static int unuse;
	if(a==1)
	{	
	    unuse = a + b;
	    printf("%d",unuse); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
	}
}

/*
 * Types of defects: unused variable
 * Complexity: Union Member	Internal variables
 */
typedef struct {
	int a;
	int b;
} unused_var_007_s_001;

typedef struct {
	int a;
	int b;
} unused_var_007_s_002;

typedef struct {
	int a;
	int unuse;
} unused_var_007_s_003;

typedef union {
	unused_var_007_s_001 s1;
	unused_var_007_s_002 s2;
	unused_var_007_s_003 s3;
} unused_var_007_uni_001;

unused_var_007_uni_001 unused_var_007_uni_001_gbl;
void unused_var_007 ()
{
	unused_var_007_uni_001_gbl.s1.a = 1;
	unused_var_007_uni_001_gbl.s1.b = 2;
	unused_var_007_uni_001_gbl.s3.a = unused_var_007_uni_001_gbl.s1.a + unused_var_007_uni_001_gbl.s1.b;/*Tool should detect this line as error*/ /*ERROR:Unused variable*/
	printf("%d",unused_var_007_uni_001_gbl.s3.a); /*Tool should not detect this line as error*/ /*No ERROR:Unused variable*/
}

/*
 * Types of defects: unused variable
 * unused variable main function
 */
extern volatile int vflag;
void unused_var_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		unused_var_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		unused_var_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		unused_var_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		unused_var_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		unused_var_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		unused_var_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		unused_var_007();
	}
}
