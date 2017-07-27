/********Software Analysis - FY2013*************/
/*
* File Name: wrong_arguments_func_pointer.c
* Defect Classification
* ---------------------
* Defect Type: Pointer related defects
* Defect Sub-type: Comparison NULL with function pointer
* Description: Defect Free Code to identify false positives to identify the wrong arguments fed into a function pointer
*  Created on: Oct 8, 2013
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

float (*func_glb)(float);
char **wrong_arguments_func_pointer_015_dst1_gbl=NULL;

int (*wrong_arguments_func_pointer_017_func_gbl)(int flag,float flag2 );

#define MAX 10
typedef struct {
    int arr[MAX];
    int a;
    int b;
    int c;
} wrong_arguments_func_pointer_018_s_001;

void (*wrong_arguments_func_pointer_018_fptr_gbl)(wrong_arguments_func_pointer_018_s_001*);

void (*wrong_arguments_func_pointer_018_fptr1_gbl)(wrong_arguments_func_pointer_018_s_001,wrong_arguments_func_pointer_018_s_001 *);
void (*wrong_arguments_func_pointer_018_fptr2_gbl)(wrong_arguments_func_pointer_018_s_001 *,int);
int func_pointer_018_global_set=0;

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one
* (function : int and function pointer :int *).
* The type of return value is int .
*/
int wrong_arguments_func_pointer_001_func_001(int a)
{
    int i=10;
	return (i);
}

void wrong_arguments_func_pointer_001 ()
{
	int arr[5] = {1,2,3,4,5} ;
	int (*fptr)(int);
	int a;
	fptr = wrong_arguments_func_pointer_001_func_001;
	a =fptr(arr[0]); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one.
* (function : int and function pointer : char *).
* The type of return value is int
*/
int wrong_arguments_func_pointer_002_func_001(int a)
{
    int i=20;
	return (i);
}

void wrong_arguments_func_pointer_002 ()
{
	char buf[10] = "string";
	int (*fptr)(int);
	int a;
	fptr = wrong_arguments_func_pointer_002_func_001;
	a =fptr(buf[0]); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one.
* (function : int * and function pointer : int).
* The type of return value is int
*/
int wrong_arguments_func_pointer_003_func_001 (int *p)
{
	return (*p);
}

void wrong_arguments_func_pointer_003 ()
{
	int (*func)(int*);
	int a = 1;
	int ret;
	func = wrong_arguments_func_pointer_003_func_001;
	ret = func(&a); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one.
*(function : char * and function pointer : float).
* The type of return value is char
*/
char wrong_arguments_func_pointer_004_func_001 (char *p)
{
	return (*p);
}

void wrong_arguments_func_pointer_004 ()
{
    char (*func)(char*);
	char buf[10] = "string";
	char ret;
	func = wrong_arguments_func_pointer_004_func_001;
	ret = func(buf); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
*Complexity: Different argument types and the number of argument is one.
*(function : char * and function pointer : float *).
* The type of return value is float
*/
float wrong_arguments_func_pointer_005_func_001 (char *p)
{
	float f=20.5;
	if((strcmp(p,"string")) == 0)
	{
		f++;
	}
	return (f);
}

void wrong_arguments_func_pointer_005 ()
{
    float (*func)(char*);
	char buf[10] = "string";
	float ret;
	func = wrong_arguments_func_pointer_005_func_001;
	ret = func(buf); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different numbers of arguments and the number of argument is one
* (function : two int arguments and function pointer : one int argument).
* The type of return value is int .
*/
int wrong_arguments_func_pointer_006_func_001 (int a, int b)
{
	return a + b;
}

void wrong_arguments_func_pointer_006 ()
{
	int (*func)(int, int);
	int ret;
	func = wrong_arguments_func_pointer_006_func_001;
	ret = func(1, 2); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different numbers of arguments and the number of argument is two.
* (function : one double argument and function pointer : two double arguments).
* The type of return value is unsigned int
*/
unsigned int wrong_arguments_func_pointer_007_func_001 (double a)
{
	a++;
	return ((unsigned int)(a));
}

void wrong_arguments_func_pointer_007 ()
{
	unsigned int (*func)(double);
	unsigned int ret;
	func = wrong_arguments_func_pointer_007_func_001;
	ret = func(10.005); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different numbers of arguments and the number of argument is two.
* (function : one float argument and function pointer : two char pointer arguments).
* The type of return value is float
*/
float wrong_arguments_func_pointer_008_func_001(float a )
{
	a--;
	return a;
}
void wrong_arguments_func_pointer_008 ()
{
    float a = 11.5;
	float ret;
	func_glb = wrong_arguments_func_pointer_008_func_001;
	ret = func_glb(a); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different numbers of arguments and the number of argument is three.
* (function : 3 Char pointer arguments and function pointer : two char arguments,one int argument).
* The type of return value is float
*/
char wrong_arguments_func_pointer_009_func_001(char *str1, char *str2, char*str3)
{
    strcpy(str1,str2);
    strcpy(str3,str1);
    return ('c');
}

void wrong_arguments_func_pointer_009 ()
{
  char *str1 = strdup("STRING33");
  if (!str1) return;
  char *str2 = strdup("STRING55");
  if (!str2) return;
  char *str3 = (char *) malloc(20*sizeof(char));
  if (!str3) return;
  char ret;
  char (*func)(char *,char *, char *);
  func = wrong_arguments_func_pointer_009_func_001;
  ret = func(str1,str2,str3); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
  free(str1);
  free(str2);
  free(str3);
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one
* (function : structure pointer and function pointer :structure).
* The type of return value is void .
*/
typedef struct {
    int a;
    int b;
} wrong_arguments_func_pointer_010_s_001;

void wrong_arguments_func_pointer_010_func_001(wrong_arguments_func_pointer_010_s_001* st)
{
    memset(st, 0, sizeof(*st));
    st->a = 1;
    st->b=2;
}

void wrong_arguments_func_pointer_010 ()
{
 	wrong_arguments_func_pointer_010_s_001 st;
	void (*fptr)(wrong_arguments_func_pointer_010_s_001*);
	fptr = wrong_arguments_func_pointer_010_func_001;
	fptr(&st); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one
* (function : structure pointer and function pointer :structure).
* one function pointer used multiple times
* The type of return value is void .
*/
#define MAX 10
typedef struct {
    int arr[MAX];
    int a;
    int b;
    int c;
} wrong_arguments_func_pointer_011_s_001;

void wrong_arguments_func_pointer_011_func_001(wrong_arguments_func_pointer_011_s_001* st)
{
    memset(st, 0, sizeof(*st));
    st->a = 1;
}

void wrong_arguments_func_pointer_011_func_002(wrong_arguments_func_pointer_011_s_001 *st)
{
    int temp;
    int i;
    for (i = 0; i < MAX; i++)
    {
    	st->arr[i] = i;
    	temp = st->arr[i];
    }
}

void wrong_arguments_func_pointer_011_func_003(wrong_arguments_func_pointer_011_s_001 *st)
{
    st->b = st->c;
}

void wrong_arguments_func_pointer_011 ()
{
 	wrong_arguments_func_pointer_011_s_001 st;
	void (*fptr)(wrong_arguments_func_pointer_011_s_001*);
	fptr = wrong_arguments_func_pointer_011_func_001; /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
	fptr(&st);
	fptr = wrong_arguments_func_pointer_011_func_002;
	fptr(&st);
	fptr = wrong_arguments_func_pointer_011_func_003;
	fptr(&st);
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one
* (function : structure pointer and function pointer :structure).
* one function pointer used multiple times with different argument function
* The type of return value is void .
*/
#define MAX 10
typedef struct {
    int arr[MAX];
    int a;
    int b;
    int c;
} wrong_arguments_func_pointer_012_s_001;

void wrong_arguments_func_pointer_012_func_001(wrong_arguments_func_pointer_012_s_001* st)
{
    memset(st, 0, sizeof(*st));
    st->a = 1;
}

void wrong_arguments_func_pointer_012_func_002(wrong_arguments_func_pointer_012_s_001 st,wrong_arguments_func_pointer_012_s_001* st1)
{
    int temp=0;
    int i;
    memset(st1, 0, sizeof(*st1));
    for (i = 0; i < MAX; i++)
    {
    	st.arr[i] = i;
    	st1->arr[i] = st.arr[i]+i;
    	temp += st.arr[i];
    }
}

void wrong_arguments_func_pointer_012_func_003(wrong_arguments_func_pointer_012_s_001 *st, int a)
{
    st->b = st->c+a;
}

void wrong_arguments_func_pointer_012 ()
{
	wrong_arguments_func_pointer_012_s_001 st,*st1;
	st1 = (wrong_arguments_func_pointer_012_s_001 *)malloc(1*sizeof(wrong_arguments_func_pointer_012_s_001));

	void (*fptr)(wrong_arguments_func_pointer_012_s_001*);
	fptr = wrong_arguments_func_pointer_012_func_001;
	fptr(&st); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/

	void (*fptr1)(wrong_arguments_func_pointer_012_s_001,wrong_arguments_func_pointer_012_s_001 *);
	fptr1 = wrong_arguments_func_pointer_012_func_002;
	fptr1(st,st1);

	void (*fptr2)(wrong_arguments_func_pointer_012_s_001 *,int);
	fptr2 = wrong_arguments_func_pointer_012_func_003;
	fptr2(&st,1);
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is two
* (function : int, char double pointer and function pointer :char pointer).
* The type of return value is void .
*/
void wrong_arguments_func_pointer_013_func_001 (int len,char **stringPtr)
{
	char * p = malloc(sizeof(char) * (len+1));
	*stringPtr = p;
}

void wrong_arguments_func_pointer_013 ()
{
 	char *str = "This is a string";
	char *str1;
	void (*fptr)(int,char **);
	fptr = wrong_arguments_func_pointer_013_func_001;
	fptr(strlen(str),&str1); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
	strcpy(str1,str);
	free(str1);
	str1 = NULL;
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is two
* (function : long array, int and function pointer :float pointer).
* The type of return value is int
*/
int wrong_arguments_func_pointer_014_func_001(int flag)
{
   int ret ;
   if (flag ==0)
	   ret = 0;
   else
	   ret=1;
   return ret;
}

long wrong_arguments_func_pointer_014_func_002 (long a[],int max)
{
	int i;
	for(i=0;i<max;i++)
	{
		a[i] = i;
	}
	return a[i];
}

void wrong_arguments_func_pointer_014 ()
{
  long arr[5];
  if(wrong_arguments_func_pointer_014_func_001(0) == 0)
    {
      long (*fptr)(long [],int);
      long a;
      fptr = wrong_arguments_func_pointer_014_func_002;
      a =fptr(arr,5); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
    }
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is two
* (function : double pointer to char , pointer to char array and function pointer :double pointer to char).
* The type of return value is void
*/
void wrong_arguments_func_pointer_015_func_002(char **wrong_arguments_func_pointer_015_dst1_gbl, char (*src)[15])
{
	int i;
	for(i=0;i<5;i++)
	{
	   strcpy(*(wrong_arguments_func_pointer_015_dst1_gbl+i),src[i]);
	}
}

void wrong_arguments_func_pointer_015 ()
{
    char str2[][15] = {{"STRING"},
    		       {"TEST"},{"STRING#"},{"TEST!"},{"TRIAL"}};
	int i;
	wrong_arguments_func_pointer_015_dst1_gbl = (char**) malloc(5*sizeof(char*));
    for(i=0;i<5;i++)
    {
    	wrong_arguments_func_pointer_015_dst1_gbl[i]=(char*) malloc(15*sizeof(char));
    }
	while(1)
	{
		void (*fptr)(char **,char (*)[]);
	    fptr = wrong_arguments_func_pointer_015_func_002;
	    fptr(wrong_arguments_func_pointer_015_dst1_gbl,str2); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
	    break;
	}
	for(i=0;i<5;i++)
    {
		free(wrong_arguments_func_pointer_015_dst1_gbl[i]);
        wrong_arguments_func_pointer_015_dst1_gbl[i] = NULL;
    }
    free(wrong_arguments_func_pointer_015_dst1_gbl);
    wrong_arguments_func_pointer_015_dst1_gbl = NULL;
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different numbers of arguments and the number of argument is three.
* (function : 3 Char pointer arguments and function pointer : two char arguments,one int argument).
* The type of return value is float
*/
char wrong_arguments_func_pointer_016_func_001(char *str1, int *str2, float*str3)
{
  char s[20];
  strcpy(s,str1);
  *str2 +=1;
  *str3 +=1;
  return (*str2);
}
void wrong_arguments_func_pointer_016 ()
{
  char *str1 = "STRING";
  int a=10,*str2 = &a;
  float f=20.5,*str3 = &f;
  char ret;
  char (*func)(char *,int *, float *);
  func = wrong_arguments_func_pointer_016_func_001; /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
  ret = func(str1,str2,str3);
}

/*
 * Type of defect: Wrong arguments passed to a function pointer
 * Complexity: different return type function :int and typedef and function pointer: int *,void(int)
 * Global function pointer returns different type and takes different parameter
 */
int wrong_arguments_func_pointer_017_func_001 (int flag,float flag2)
{
	float a=0.0;
	a += flag2;
	flag = 1;
	return flag;
}

int wrong_arguments_func_pointer_017_func_002 (int flag,float flag2)
{
	int ret = 0;
	if (flag == 1)
	{
		goto my_label;
	}

	return ret;

my_label:
    if (flag == 1)
	{
    	wrong_arguments_func_pointer_017_func_gbl = wrong_arguments_func_pointer_017_func_001;

        goto my_label2;
 	ret ++;
	}

my_label2:
    if (flag == 1)
 	{
          flag = wrong_arguments_func_pointer_017_func_gbl(0,1.9); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
          flag2++;
 	}
	return ret;
}

void wrong_arguments_func_pointer_017 ()
{
    int flag;
    int (*fptr)(int,float);
    fptr =wrong_arguments_func_pointer_017_func_002;
    flag = fptr(1,4.5);
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity: Different argument types and the number of argument is one
* (function : structure pointer and function pointer :structure).
* one function pointer used multiple times with different argument and different return type
* The type of return value is void .
*/
void wrong_arguments_func_pointer_018_func_001(wrong_arguments_func_pointer_018_s_001* st)
{
    memset(st, 0, sizeof(*st));
    st->a = 1;
    func_pointer_018_global_set = 1;
}

void wrong_arguments_func_pointer_018_func_002(wrong_arguments_func_pointer_018_s_001 st,wrong_arguments_func_pointer_018_s_001* st1)
{
    int temp=0;
    int i;
    for (i = 0; i < MAX; i++)
    {
    	st.arr[i] = i;
    	st1->arr[i] = st.arr[i]+i;
    	temp += st.arr[i];
    }
}

void wrong_arguments_func_pointer_018_func_003(wrong_arguments_func_pointer_018_s_001 *st, int a)
{
    st->b = st->c+a;
}

void wrong_arguments_func_pointer_018_func_004(wrong_arguments_func_pointer_018_s_001 st,wrong_arguments_func_pointer_018_s_001* st1)
{
	if (func_pointer_018_global_set == MAX)
	{
		wrong_arguments_func_pointer_018_fptr1_gbl = wrong_arguments_func_pointer_018_func_002;
		wrong_arguments_func_pointer_018_fptr1_gbl(st,st1); /*Tool should not detect this line as error*//*No ERROR:Wrong arguments passed to a function pointer*/
	}
	else
	{
		wrong_arguments_func_pointer_018_fptr2_gbl = wrong_arguments_func_pointer_018_func_003;
		wrong_arguments_func_pointer_018_fptr2_gbl(&st,1);
	}
}

void wrong_arguments_func_pointer_018 ()
{
	wrong_arguments_func_pointer_018_s_001 st,*st1;
	st1 = (wrong_arguments_func_pointer_018_s_001 *)malloc(1*sizeof(wrong_arguments_func_pointer_018_s_001));
    memset(st1, 0, sizeof(*st1));

    wrong_arguments_func_pointer_018_fptr_gbl = wrong_arguments_func_pointer_018_func_001;
    wrong_arguments_func_pointer_018_fptr_gbl(&st);

	void (*fptr3)(wrong_arguments_func_pointer_018_s_001 st,wrong_arguments_func_pointer_018_s_001* st1);
	fptr3 = wrong_arguments_func_pointer_018_func_004;
	fptr3(st,st1);
}

/*
* Type of defect: Wrong arguments passed to a function pointer
* Complexity:Wrong arguments passed to a function pointer main function
*/
extern volatile int vflag;
void wrong_arguments_func_pointer_main ()
{
	if (vflag == 1 || vflag ==888)
	{
		wrong_arguments_func_pointer_001 ();
	}

	if (vflag == 2 || vflag ==888)
	{
		wrong_arguments_func_pointer_002 ();
	}

	if (vflag == 3 || vflag ==888)
	{
		wrong_arguments_func_pointer_003 ();
	}

	if (vflag == 4 || vflag ==888)
	{
		wrong_arguments_func_pointer_004 ();
	}

	if (vflag == 5 || vflag ==888)
	{
		wrong_arguments_func_pointer_005 ();
	}

	if (vflag == 6 || vflag ==888)
	{
		wrong_arguments_func_pointer_006 ();
	}

	if (vflag == 7 || vflag ==888)
	{
		wrong_arguments_func_pointer_007 ();
	}

	if (vflag == 8 || vflag ==888)
	{
		wrong_arguments_func_pointer_008 ();
	}

	if (vflag == 9 || vflag ==888)
	{
		wrong_arguments_func_pointer_009 ();
	}

	if (vflag == 10 || vflag ==888)
	{
		wrong_arguments_func_pointer_010 ();
	}

	if (vflag == 11 || vflag ==888)
	{
		wrong_arguments_func_pointer_011 ();
	}

	if (vflag == 12 || vflag ==888)
	{
		wrong_arguments_func_pointer_012 ();
	}

	if (vflag == 13 || vflag ==888)
	{
		wrong_arguments_func_pointer_013 ();
	}

	if (vflag == 14 || vflag ==888)
	{
		wrong_arguments_func_pointer_014 ();
	}

	if (vflag == 15 || vflag ==888)
	{
		wrong_arguments_func_pointer_015 ();
	}

	if (vflag == 16 || vflag ==888)
	{
		wrong_arguments_func_pointer_016 ();
	}

	if (vflag == 17 || vflag ==888)
	{
		wrong_arguments_func_pointer_017 ();
	}

	if (vflag == 18 || vflag ==888)
	{
		wrong_arguments_func_pointer_018 ();
	}
}

