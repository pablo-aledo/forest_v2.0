/********Software Analysis - FY2013*************/
/*
* File Name: invalid_extern.c
* Defect Classification
* ---------------------
* Defect Type: Misc defects
* Defect Sub-type: Bad extern type for global variable
* Description: Defect Free Code to identify false positives during invalid extern declaration
*/

/*
 * Types of defects: external variable type mistake
 * Complexity: external variable type error
 * Note: the PolySpace compilation error handling
 *       (variable has incompatible type with its ... The following)
 */
/* #if ! (defined(CHECKER_POLYSPACE) || defined(CHECKER_VARVEL)) */
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
extern int invalid_extern_001_glb_buf[5]; /*Tool should not detect this line as error*/ /*No ERROR:Bad extern type for global variable*/
extern float invalid_extern_001_glb_float[5] ; /*Tool should not detect this line as error*/ /*No ERROR:Bad extern type for global variable*/
extern float invalid_extern_001_glb_var3[5] ; /*Tool should not detect this line as error*/ /*No ERROR:Bad extern type for global variable*/
extern int invalid_extern_001_glb_var4 ; /*Tool should not detect this line as error*/ /*No ERROR:Bad extern type for global variable*/
extern float invalid_extern_001_glb_var5 ; /*Tool should not detect this line as error*/ /*No ERROR:Bad extern type for global variable*/

typedef struct {
        int  csr;
        int  data;
}invalid_extern_001_glb_006_s_001;

extern invalid_extern_001_glb_006_s_001 *invalid_extern_001_glb_006_str;


void invalid_extern_001 ()
{
	invalid_extern_001_glb_buf[3] = 1;
}

void invalid_extern_002 ()
{
	invalid_extern_001_glb_float[3] = 1.0;
}

void invalid_extern_003 ()
{
	invalid_extern_001_glb_var3[3] = 1.0;
}

void invalid_extern_004 ()
{
	invalid_extern_001_glb_var4 = 1;
}

void invalid_extern_005 ()
{
	invalid_extern_001_glb_var5 = 1.0;
}

void invalid_extern_006 ()
{
	invalid_extern_001_glb_006_str = (invalid_extern_001_glb_006_s_001 *) malloc(1*sizeof(invalid_extern_001_glb_006_s_001));
	invalid_extern_001_glb_006_str->csr = 10;
}

/* #endif ! (defined(CHECKER_POLYSPACE) || defined(CHECKER_VARVEL)) */

/*
 * Types of defects: external variable type mistake
 * Complexity: volatile
 */
extern volatile int vflag;
void invalid_extern_main ()
{
/*#if ! (defined(CHECKER_POLYSPACE) || defined(CHECKER_VARVEL))*/
	if (vflag == 1 || vflag ==888)
	{
		invalid_extern_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		invalid_extern_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		invalid_extern_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		invalid_extern_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		invalid_extern_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		invalid_extern_006();
	}
/*#endif */ /* ! (defined(CHECKER_POLYSPACE) || defined(CHECKER_VARVEL)) */
}
