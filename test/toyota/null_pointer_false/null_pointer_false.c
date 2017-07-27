/********Software Analysis - FY2013*************/
/*
* File Name: null_pointer.c
* Defect Classification
* ---------------------
* Defect Type: Pointer related defects
* Defect Sub-type: Dereferencing a NULL pointer
*
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
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Constant value to NULL single pointer
 */
void null_pointer_001 ()
{
	int *p = NULL;
	*p = 1; /*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Constant value to NULL double pointer
 */
void null_pointer_002 ()
{
	int *p = NULL;
	int ret;
	ret = *p;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
        sink = ret;
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Constant value to NULL single pointer
 */
void null_pointer_003 ()
{
	int **pp;
	int *p = NULL;
	pp = &p;
	**pp = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Constant value to NULL struct pointer
 */
typedef struct {
	int a;
	int b;
	int c;
} null_pointer_004_s_001;

void null_pointer_004 ()
{
	null_pointer_004_s_001 *p = NULL;
	p->a = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Constant value to NULL union pointer
 */
typedef struct {
	int a;
	int b;
} null_pointer_005_s_001;

typedef struct {
	int a;
	int b;
} null_pointer_005_s_002;

typedef struct {
	int a;
	int b;
} null_pointer_005_s_003;

typedef union {
	null_pointer_005_s_001 s1;
	null_pointer_005_s_002 s2;
	null_pointer_005_s_003 s3;
} null_pointer_005_uni_001;

void null_pointer_005 ()
{
	null_pointer_005_uni_001 *p = NULL;
	p->s1.a = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: Assign a Value of random variable to NULL single pointer
 */
void null_pointer_006 ()
{
	int *p;
	p = (int *)(intptr_t)rand();
	*p = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: single pointer Linear equation expressions	Write
 */
void null_pointer_007 ()
{
	int *p;
	int a = 3;
	p = (int *)(intptr_t)((2 * a) - 6);
	*p = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : NULL pointer dereference (access)
 * Complexity: single pointer The return value of the function	expressions	Write
 */
int* null_pointer_008_func_001 ()
{
	return NULL;
}

void null_pointer_008 ()
{
	int *p;
	p = null_pointer_008_func_001();
	*p = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : pointer reference (access)
 * Complexity: single pointer Function arguments	expressions	Write
 */
void null_pointer_009_func_001 (int *p)
{
	*p = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

void null_pointer_009 ()
{
	null_pointer_009_func_001(NULL);
}

/*
 * Defect types : pointer reference (access)
 * Complexity: single pointer  1 alias 	expressions	Write
 */
void null_pointer_010 ()
{
	int *p = NULL;
	int *p1;
	p1 = p;
	*p1 = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
 * Defect types : pointer reference (access)
 * Complexity: single pointer double alias	expressions	Write
 */
void null_pointer_011 ()
{
	int *p = NULL;
	int *p1;
	int *p2;
	p1 = p;
	p2 = p1;
	*p2 = 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}


void null_pointer_012 ()
{
	int *p = NULL;
	p[3] = 1; /*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

int *null_pointer_013_func_001 (void)
{
	return (NULL);
}

void null_pointer_013 ()
{
	int *p;
	p = null_pointer_013_func_001();
	if (p != NULL)
	{
		*p = 1;
	}
	*p = 2;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
}

/*
  * Types of defects: NULL pointer dereference (access)
  * Complexity: NULL pointer access check after function call
*/

int *null_pointer_014_func_001 (void)
{
	return (NULL);
}

void null_pointer_014 ()
{
	int *p;
	p = null_pointer_014_func_001();
	*p = 1; /*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
	if (p != NULL)
	{
		*p = 2;
	}
}

/*
* Types of defects: NULL pointer dereference (access)
 *  Memory allocated in a function and Memory used in another function
 */
# define INDEX 'a'
static unsigned char a =INDEX;
char * null_pointer_015_gbl_ptr;
void null_pointer_015_func_001 (int len)
{
	null_pointer_015_gbl_ptr=NULL;
	if(a != INDEX)
		null_pointer_015_gbl_ptr= malloc(sizeof(char) * (len+1));
}

void null_pointer_015 ()
{
	char *str = "This is a string";
	null_pointer_015_func_001(strlen(str));
	strcpy(null_pointer_015_gbl_ptr,str);/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
	free(null_pointer_015_gbl_ptr);
	null_pointer_015_gbl_ptr = NULL;
}

/*
* Types of defects: NULL pointer dereference (access)
* Complexity: When using a double pointer to long , memory allocated in another function inside goto label and if condition
*/
long ** null_pointer_016_gbl_doubleptr;
int null_pointer_016_func_001(int flag)
{
   int ret ;
   if (flag ==0)
	   ret = 0;
   else
	   ret=1;
   return ret;
}
void null_pointer_016_func_002()
{
	int i,j;
	null_pointer_016_gbl_doubleptr=(long**) malloc(10*sizeof(long*));

	for(i=0;i<10;i++)
	{
		null_pointer_016_gbl_doubleptr[i]=(long*) malloc(10*sizeof(long));
	}
	for(i=0;i<10;i++)
	{
		for(j=0;j<10;j++)
		{
			null_pointer_016_gbl_doubleptr[i][j]=i;
		}
	}
}

#define ZERO 0
void null_pointer_016()
{
	int flag=0,i,j;
	null_pointer_016_gbl_doubleptr=NULL;
goto label;

    if(null_pointer_016_func_001(flag)==ZERO)
	{
		for(i=0;i<10;i++)
		{
			for(j=0;j<10;j++)
			{
				null_pointer_016_gbl_doubleptr[i][j] += 1;/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
			}
			free (null_pointer_016_gbl_doubleptr[i]);
			null_pointer_016_gbl_doubleptr[i] = NULL;
	   }
	    free(null_pointer_016_gbl_doubleptr);
	    null_pointer_016_gbl_doubleptr = NULL;
	}

label:
    	if(null_pointer_016_func_001(flag)!=ZERO)
    	{
    		null_pointer_016_func_002();
    	}
}

/*
* Types of defects: NULL pointer dereference (access)
* Complexity: When using a double pointer to char in an infinite while loop
*/
/*Allocate Memory */
char **null_pointer_017dst;

void null_pointer_017_func_001(int flag)
{
	null_pointer_017dst = NULL;
	int i;
    {
		while(flag)
		{
			null_pointer_017dst = (char**) malloc(5*sizeof(char*));
		    for(i=0;i<5;i++)
		    {
		    	null_pointer_017dst[i]=(char*) malloc(15*sizeof(char));
		    }
		    break;
		}
    }
}

void null_pointer_017 ()
{
	int i;
    null_pointer_017_func_001(0);
    for(i=0;i<5;i++)
    {
    	strcpy (null_pointer_017dst[i],"STRING");/*Tool should detect this line as error*/ /*ERROR:NULL pointer dereference*/
    }
	while(1)
	{
		for(i=0;i<5;i++)
	    {
			free(null_pointer_017dst[i]);
			null_pointer_017dst[i] = NULL;
	    }
	    free(null_pointer_017dst);
	    null_pointer_017dst = NULL;
	    break;
	}
}

/*
 *Types of defects: NULL pointer dereference (access)
 *Complexity: Volatile
 */
extern volatile int vflag;
void null_pointer_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		null_pointer_001();
	}

	if (vflag == 2 || vflag ==888)
	{
		null_pointer_002();
	}

	if (vflag == 3 || vflag ==888)
	{
		null_pointer_003();
	}

	if (vflag == 4 || vflag ==888)
	{
		null_pointer_004();
	}

	if (vflag == 5 || vflag ==888)
	{
		null_pointer_005();
	}

	if (vflag == 6 || vflag ==888)
	{
		null_pointer_006();
	}

	if (vflag == 7 || vflag ==888)
	{
		null_pointer_007();
	}

	if (vflag == 8 || vflag ==888)
	{
		null_pointer_008();
	}

	if (vflag == 9 || vflag ==888)
	{
		null_pointer_009();
	}

	if (vflag == 10 || vflag ==888)
	{
		null_pointer_010();
	}

	if (vflag == 11 || vflag ==888)
	{
		null_pointer_011();
	}

	if (vflag == 12 || vflag ==888)
	{
		null_pointer_012();
	}

	if (vflag == 13 || vflag ==888)
	{
		null_pointer_013();
	}

	if (vflag == 14 || vflag ==888)
	{
		null_pointer_014();
	}

	if (vflag == 15 || vflag ==888)
	{
		null_pointer_015();
	}

	if (vflag == 16 || vflag ==888)
	{
		null_pointer_016();
	}

	if (vflag == 17 || vflag ==888)
	{
		null_pointer_017();
	}
}
