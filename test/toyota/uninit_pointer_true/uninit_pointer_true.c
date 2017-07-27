/********Software Analysis - FY2013*************/
/*
* File Name: uninit_pointer.c
* Defect Classification
* ---------------------
* Defect Type: Pointer related defects
* Defect Sub-type: Uninitialized pointer
* Description: Defect Free Code to identify false positives to identify uninitialized pointer access in the code flow
*/
/*
 * uninit_pointer.c
 *
 *  Created on: Sep 20, 2013
 *      Author: hemalatha
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

char ** uninit_pointer_016_gbl_doubleptr;
/*
* Types of defects: Uninitialized pointer
* Complexity: When using a single pointer int	Variable - Loading
*/
void uninit_pointer_001 ()
{
	int a = 5;
	int *p = &a;
	int ret;
	ret = *p; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
        sink = ret;
}

/*
* Types of defects: Uninitialized pointer
* Complexity: 1 single pointer	int	Variable	Write
*/
void uninit_pointer_002 ()
{
	int a =30;
	int *p = &a;
	*p = 1;  /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

/*
* Types of defects: Uninitialized pointer
* Complexity: When using a double pointer	int	Variable	Write
*/
void uninit_pointer_003 ()
{
	int **pp = NULL;
	int *p = NULL;
	int a = 20;
	int ret;
	p = &a;
	pp = &p;
	ret = **pp; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
        sink = ret;
}

/*
* Types of defects: Uninitialized pointer
* Complexity: 1 single pointer	int	Function arguments	Loading
*/
void uninit_pointer_004_func_001 (int *p)
{
	int ret=10;
	*p = ret;
        sink = ret;
}
void uninit_pointer_004 ()
{
	int a = 10;
	int *p = &a;
	uninit_pointer_004_func_001(p); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

/*
* Types of defects: Uninitialized pointer
* Complexity: pointer arrays	int	Function arguments	Loading
*/
void uninit_pointer_005_func_001 (int *pbuf[])
{
	int buf1[6] = {1, 2, 3, 4, 5, 6};
	int buf2[6] = {1, 2, 3, 4, 5, 6};
	int buf3[6] = {1, 2, 3, 4, 5, 6};
	int buf4[6] = {1, 2, 3, 4, 5, 6};
	int buf5[6] = {1, 2, 3, 4, 5, 6};
	pbuf[0] = buf1;
	pbuf[1] = buf2;
	pbuf[2] = buf3;
	pbuf[3] = buf4;
	pbuf[4] = buf5;
	int ret;
	ret = pbuf[1][1];
        sink = ret;

}
void uninit_pointer_005 ()
{
	int *pbuf[5];
	uninit_pointer_005_func_001(pbuf); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

/*
* Types of defects: Uninitialized pointer
* Complexity: double pointer int	Function arguments	Write
*/
void uninit_pointer_006_func_001 (int **pp)
{
	**pp = 1; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

void uninit_pointer_006 ()
{
	int a =10;
	int *p = &a;
	uninit_pointer_006_func_001(&p);
}

/*
* Types of defects: Uninitialized pointer
* Complexity: When using a double char pointer arrays
*/
void uninit_pointer_007 ()
{
        char *buf1=strdup("String1");
	char *buf2=strdup("String2");
	char *buf3=strdup("String3");
	char *buf4=strdup("String4");
	char *buf5=strdup("String5");
        if (!buf1 || !buf2 || !buf3 || !buf4 || !buf5) return;
	char **pbuf[5] = {&buf1, &buf2, &buf3, &buf4, &buf5};
	int i,j=4;

	for(i=0;i<5;i++)
	{
          *((*pbuf[i])+j)='a'; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
	    printf("uninit %c \n",*((*pbuf[i])+j));
	}
        free(buf1);
        free(buf2);
        free(buf3);
        free(buf4);
        free(buf5);
}

/*
* Types of defects: Uninitialized pointer
* Complexity: structure	int	Function arguments	Loading
*/
typedef struct {
	int a;
	int b;
	int uninit;
} uninit_pointer_008_s_001;

void uninit_pointer_008_func_001 (uninit_pointer_008_s_001 *p)
{
	int ret = 10;
	p->uninit = ret;
}
void uninit_pointer_008 ()
{
	uninit_pointer_008_s_001 s;
	s.a = 1;
	s.b = 1;
	s.uninit = 1;
	uninit_pointer_008_func_001(&s); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

/*
* Types of defects: Uninitialized pointer
* Complexity: When using a pointer to char and initialized based on return value of function
*/
int uninit_pointer_009_func_001(int flag)
{
   int ret;
   if (flag ==0)
	   ret = 0;
   else
	   ret=flag+1;
   return ret;
}

void uninit_pointer_009()
{
	char *buf,buf1[25];
	int flag=1;

	if(uninit_pointer_009_func_001(flag)>0)
	{
		buf = "This is a string";
	}
    if(uninit_pointer_009_func_001(flag)>0)
    {
    	strcpy(buf1,buf); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
    }
}

/*
* Types of defects: Uninitialized pointer
* Complexity: void pointer to data passed from one function to another
*/
void uninit_pointer_010_func_001 (void * vptr)
{
    /* cast void pointer to a pointer of the appropriate type */
    char * * cptr = (char * *)vptr;
    char * buf = "String";
    buf = (*cptr); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
    sink = buf[idx];
}
void uninit_pointer_010 ()
{
    void *buf1;
	buf1 = "String Test";
    uninit_pointer_010_func_001(&buf1);    
}

/*
* Types of defects: Uninitialized pointer
* Complexity: When using a unsigned int pointer and partially initialized in a infinite loop
*/
void uninit_pointer_011 ()
{
    unsigned int * ptr = NULL,a=0;
    ptr = (unsigned int *)malloc(10*sizeof(unsigned int *));
    int i;
	if (ptr!=NULL)
	{
		while(1)
       {
           for(i=0; i<10; i++)
           {
            	ptr[i] = i;
           }
           break;
       }
       while(1)
       {
          for(i=0; i<10; i++)
          {
        	  a += ptr[i]; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
          }
          break;
       }
	}
}

/*
* Types of defects: Uninitialized pointer
* Complexity: When using a pointer to float , pointing to 1D array
*/
void uninit_pointer_012 ()
{
	float * fptr =NULL;
	float arr[10];
	fptr = arr;
	int i;
	for(i=0; i<10; i++)
	{
		fptr[i] = (float)i;
	}
	for(i=0; i<10; i++)
	{
		arr[i] = ++fptr[i]; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
	}
}

/*
* Types of defects: Uninitialized pointer
* Complexity: Double int pointer partially initialized with 2D array
*/
void uninit_pointer_013 ()
{
	int **ptr = (int**) malloc(3*sizeof(int*));
		int i,j;

		for(i=0;i<3;i++)
			ptr[i]=(int*) malloc(3*sizeof(int));
	    int arr[3][3] = {{1,2,3},
				         {11,12,13},
		                 {21,22,23}};

		for(i=0;i<3;i++)
		{
			for(j=0;j<3;j++)
			{
				*(*(ptr+i)+j)= arr[i][j]; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
			}
		    free(ptr[i]);
		    ptr[i] = NULL;
		}
		free(ptr);
		ptr = NULL;
}

/*
 * Types of defects: uninitialized variable
 * Complexity: Structure passed as function parameter and based on the return value of function another structure is initialized
 */
typedef struct {
	int a;
	int b;
	int uninit;
} uninit_pointer_014_s_001;

uninit_pointer_014_s_001 *s;
void uninit_pointer_014_func_001 (int flag)
{
	switch (flag)
	{
		case 1:
		{
			s = (uninit_pointer_014_s_001 *)calloc(1,sizeof(uninit_pointer_014_s_001));
			if(s!=NULL)
			{
				s->a = 10;
			    s->b = 10;
			    s->uninit = 10;
			}
			break;
		}
		case 2:
		{
			s = (uninit_pointer_014_s_001 *)calloc(1,sizeof(uninit_pointer_014_s_001));
			if(s!=NULL)
			{
				s->a = 20;
			    s->b = 20;
			    s->uninit = 20;
			}
			break;
		}
		default:
		{
			break;
		}

	}
}

void uninit_pointer_014 ()
{
	uninit_pointer_014_s_001 r;
	uninit_pointer_014_func_001 (1);
	if(s!=NULL)
	{
	    r = *s; /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
	    free(s);
	}
        r.a = 0;
        sink = r.a;
}

/*
* Types of defects: Uninitialized pointer
* Complexity: int variable initialized with function return value using enumeration
 */
typedef enum
            {ZERO,
	         ONE,
	         TWO } values;

void uninit_pointer_015_func_001 (int *ptr )
{
	values val = ONE;
	*ptr = val;
}

void uninit_pointer_015 ()
{
    int  a=0, *ptr = &a;
    uninit_pointer_015_func_001(ptr); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
}

/*
* Types of defects: Uninitialized pointer
* Complexity: global char double pointer int variable initialized in another function
 */
int uninit_pointer_016_func_001(int flag)
{
   int ret;
   if (flag ==0)
	   ret = 0;
   else
	   ret=1;
   return ret;
}

void uninit_pointer_016_func_002()
{
	int i;
	if(uninit_pointer_016_func_001(0)==0)
	{
		uninit_pointer_016_gbl_doubleptr=(char**) malloc(10*sizeof(char*));
    	for(i=0;i<10;i++)
	    {
    		uninit_pointer_016_gbl_doubleptr[i]=(char*) malloc(10*sizeof(char));
    		   strcpy(uninit_pointer_016_gbl_doubleptr[i],"STRING00");
	    }
	}
}

void uninit_pointer_016()
{
	int flag=0,i;
	char *s=(char*) malloc(10*sizeof(char));
	if(uninit_pointer_016_func_001(flag)==0)
	{
		uninit_pointer_016_func_002();
	}

	if(uninit_pointer_016_gbl_doubleptr!=NULL)
	{
		for(i=0;i<10;i++)
		{
			if(uninit_pointer_016_gbl_doubleptr[i] !=NULL)
			{
				if(i==7)
				{
				    printf("unint p %s \n",uninit_pointer_016_gbl_doubleptr[i]);
					strcpy(s,uninit_pointer_016_gbl_doubleptr[i]); /*Tool should not detect this line as error*/ /*No ERROR:Uninitialized pointer*/
				    printf("unint p %s \n",s);
				}
				    free (uninit_pointer_016_gbl_doubleptr[i]);
			}
	    }
	    free(uninit_pointer_016_gbl_doubleptr);
	    free(s);
	}
}
/*
* Types of defects: Uninitialized pointer
* Complexity:Uninitialized pointer main function
*/
extern volatile int vflag;
void uninit_pointer_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		uninit_pointer_001 ();
	}

	if (vflag == 2 || vflag ==888)
	{
		uninit_pointer_002 ();
	}

	if (vflag == 3 || vflag ==888)
	{
		uninit_pointer_003 ();
	}

	if (vflag == 4 || vflag ==888)
	{
		uninit_pointer_004 ();
	}

	if (vflag == 5 || vflag ==888)
	{
		uninit_pointer_005 ();
	}

	if (vflag == 6 || vflag ==888)
	{
		uninit_pointer_006 ();
	}

	if (vflag == 7 || vflag ==888)
	{
		uninit_pointer_007 ();
	}

	if (vflag == 8 || vflag ==888)
	{
		uninit_pointer_008 ();
	}

	if (vflag == 9 || vflag ==888)
	{
		uninit_pointer_009 ();
	}

	if (vflag == 10 || vflag ==888)
	{
		uninit_pointer_010 ();
	}

	if (vflag == 11 || vflag ==888)
	{
		uninit_pointer_011 ();
	}

	if (vflag == 12 || vflag ==888)
	{
		uninit_pointer_012 ();
	}

	if (vflag == 13 || vflag ==888)
	{
		uninit_pointer_013 ();
	}

	if (vflag == 14 || vflag ==888)
	{
		uninit_pointer_014 ();
	}

	if (vflag == 15 || vflag ==888)
	{
		uninit_pointer_015 ();
	}

	if (vflag == 16 || vflag ==888)
	{
		uninit_pointer_016 ();
	}
}

