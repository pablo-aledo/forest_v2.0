/********Software Analysis - FY2013*************/
/*
* File Name: st_overflow.c
* Defect Classification
* ---------------------
* Defect Type: Stack related defects
* Defect Sub-type: Stack overflow
*
*/

/*	(Note) created test, assuming the maximum stack size 15 Kbytes (= 15360 bytes)	*/

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
 * Types of defects: stack overflow
 * Complexity: large internal variables
 */
void st_overflow_001 ()
{
	double buf[1048576];/* 1MB bytes */ /*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
	buf[0] = 1.0;
        sink = buf[idx];
}

 /*
* Types of defects: stack overflow
* Complexity: Level 1 - large function argument function call -
*/
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[524288];	/* 1 Mbytes */
	char buf1[65536];
	char buf2[65536];
	char buf3[65536];
	char buf4[65536];
	char buf5[65536];
	char buf6[65536];
	char buf7[65536];
	char buf8[65536];
#else
	char buf[1024];
#endif	/* Prevent failure? Correspondence */

} st_overflow_002_s_001;

void st_overflow_002_func_001 (st_overflow_002_s_001 s)
{
	s.buf[0] = 1;/*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
}

void st_overflow_002 ()
{
	st_overflow_002_s_001 s;		/* 1 Mbytes */
	st_overflow_002_func_001(s);	/* 1 Mbytes */
}

/*
 * Types of defects: stack overflow
 * Complexity: large internal variables	Large function arguments	Function call	Level 1	__
 */
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[524288];	 /* 512 Kbytes */
	char buf1[131072];  /* 128 Kbytes */
	char buf2[131072]; /* 128 Kbytes */
	char buf3[1024];
	char buf4[1024];
#else	/* Prevent failure? Correspondence */
	char buf[1024];
#endif	/* Prevent failure? Correspondence */
} st_overflow_003_s_001;

void st_overflow_003_func_001 (st_overflow_003_s_001 s)
{
	char buf[524288];					/* 512 Kbytes */ /*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
	s.buf[0] = 1;
	buf[0] = 1;
        sink = buf[idx];
}

void st_overflow_003 ()
{
	st_overflow_003_s_001 s;		/* 5 Kbytes */
	st_overflow_003_func_001(s);	/* 5 Kbytes */
}

/*
 * Types of defects: stack overflow
 * Complexity: large internal variables	Large function arguments	Function call	2 Level	__
 */
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[524288];	/* 512 Kbytes */
	char buf1[131072];/* 128 Kbytes */
	char buf2[1024];
	char buf3[1024];
#else	/* Prevent failure? Correspondence */
	char buf[1024];
	char buf1[1024];
	char buf2[1024];
#endif	/* Prevent failure? Correspondence */
} st_overflow_004_s_001;

void st_overflow_004_func_002 (st_overflow_004_s_001 s)
{
	char buf[131072];					/* 128 Kbytes */
	s.buf[0] = 1;
	buf[0] = 1;
        sink = buf[idx];
}

void st_overflow_004_func_001 (st_overflow_004_s_001 s)
{
	char buf[131072];                 /* 128 Kbytes *//*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
	buf[0] = 1;
	st_overflow_004_func_002(s);
        sink = buf[idx];
}

void st_overflow_004 ()
{
	st_overflow_004_s_001 s;
	st_overflow_004_func_001(s);
}

/*
 * Types of defects: stack overflow
 * Complexity: large internal variables	Large function arguments	Recursive function	10 Level	__ __ __ __ __ __ __ __ __ __
 */
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[262144];	/* 256 Kbytes */
#else	/* Prevent failure? Correspondence */
	char buf[1024];
#endif
} st_overflow_005_s_001;

void st_overflow_005_func_001 (st_overflow_005_s_001 s, int cnt)
{
	if (cnt > 0)
	{
		st_overflow_005_func_001(s, cnt - 1);	/* 1 Kbytes */
	}
	else
	{
		s.buf[0] = 1;/*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
	}
}

void st_overflow_005 ()
{
	char buf[4096];								/* 4 Kbytes */
	st_overflow_005_s_001 s;
	st_overflow_005_func_001(s, 10);
	buf[0] = 1;
        sink = buf[idx];
}

/*
 * Types of defects: stack overflow
 * Complexity:-	Large function arguments	Function pointer	Level 1	__
 */
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[524288];	 /* 512 Kbytes */
	char buf1[131072];  /* 128 Kbytes */
	char buf2[131072]; /* 128 Kbytes */
	char buf3[1024];
	char buf4[1024];
#else	/* Prevent failure? Correspondence */
	char buf[1024];
#endif	/* Prevent failure? Correspondence */
} st_overflow_006_s_001;

void st_overflow_006_func_001 (st_overflow_006_s_001 s)
{
	char buf[524288];	 /* 512 Kbytes */
	buf[1] = 10;
	s.buf[0] = 1;/*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
        sink = buf[idx];
}

void st_overflow_006 ()
{
	st_overflow_006_s_001 s;
	void (*func)(st_overflow_006_s_001);
	func = st_overflow_006_func_001;
	func(s);
}

/*
 * Types of defects: stack overflow
 * Complexity: large internal variables	Large function arguments	Function call	Level 1	Split condition is
 */
typedef struct {
#if 1	/* Prevent failure? Correspondence */
	char buf[524288];	 /* 512 Kbytes */
	char buf1[131072];  /* 128 Kbytes */
	char buf2[131072]; /* 128 Kbytes */
	char buf3[1024];
	char buf4[1024];
#else	/* Prevent failure? Correspondence */
	char buf[1024];
#endif	/* Prevent failure? Correspondence */
} st_overflow_007_s_001;

void st_overflow_007_func_002 (st_overflow_007_s_001 s);
void st_overflow_007_func_001 (st_overflow_007_s_001 s)
{
	char buf[262144];	/* 256 Kbytes */
	s.buf[0] = 1;
	buf[0] = 1;
	st_overflow_007_func_002(s);
        sink = buf[idx];
}

void st_overflow_007_func_002 (st_overflow_007_s_001 s)
{
	char buf[262144];	/* 256 Kbytes */
	buf[0] = 1;
	s.buf[0] = 1;/*Tool should detect this line as error*/ /*ERROR:Stack overflow*/
        sink = buf[idx];
}

void st_overflow_007 ()
{
	st_overflow_007_s_001 s;			/* 6 Kbytes */
	int flag = 10;
	if (flag)
	{
		st_overflow_007_func_001(s);	/* 6 Kbytes */
	}
	else
	{
		st_overflow_007_func_002(s);	/* 6 Kbytes */
	}
}

/*
 * Types of defects: stack overflow
 * Complexity: stack overflow main function
 */

extern volatile int vflag;
void st_overflow_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		st_overflow_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		st_overflow_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		st_overflow_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		st_overflow_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		st_overflow_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		st_overflow_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		st_overflow_007();
	}
}
