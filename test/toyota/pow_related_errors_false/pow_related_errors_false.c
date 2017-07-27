/********Software Analysis - FY2013*************/
/*
* File Name: pow_related_errors.c
* Defect Classification
* ---------------------
* Defect Type: Numerical defects
* Defect Sub-type: Power related errors
*
*/

/*
* Types of defects: Errors related to power functions
* Complexity: Very high values of number and exponent results in overflow of the answer
* * MAX VALUE of INT & LONG 2147483647 , unsigned INT & LONG 4294967295
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
* Types of defects: Errors related to power functions
* Complexity: Very high values of number and exponent results in overflow of the answer
*/

void pow_related_errors_001()
{

	double num=10^3700;
	double exponent=10^37;
	double ans;
	ans=pow(num,exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;

}

/*
* Types of defects: Errors related to power functions
* Complexity: Number not a double
*/

void pow_related_errors_002()
{
	float num=1.004;
	int exponent=3;
	double ans;
	ans=pow(num,exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;

}

/*
* Types of defects: Errors related to power functions
* Complexity: One of the elements in an array is out of bounds
* which causes the answer to go out of bounds
*/

 void pow_related_errors_003()
{
	double arr[]={2.0,1.2,3.9,10^3800,4.0};
	int i;
	double exponent=2;
	double ans;

	for(i=0;i<(sizeof(arr)/sizeof(double));i++)
	{
		double temp=arr[i];
		ans=pow(temp,exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
	}
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Usage of double pointers in pow function
*/

void pow_related_errors_004()
{
	double arr[]={2.0,1.2,3.9,10^3008,4.0};
	double* arr1=arr;
	double **arr2=&arr1;	
	double exponent=2;
	int i;
	double ans;

	for(i=0;i<5;i++)
	{
		double temp=*(*arr2+i);
		ans=pow(temp,exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
	}
        dsink = ans;

}

/*
* Types of defects: Errors related to power functions
* Complexity: Usage of pointers to access array elements
*/

void pow_related_errors_005()
{
	double arr[]={2.0,1.2,3.9,8^3800,4.0};
	double* arr1=arr;
	double exponent=2;
	int i;
	double ans;

	for(i=0;i<(sizeof(arr)/sizeof(double));i++)
	{
		double temp=arr1[i];
		ans=pow(temp,exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
	}
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Usage of a function which returns a very high value 
* causing the result to overflow
*/


double pow_related_errors_006_func_001()
{
	return 10^3800;

}

void pow_related_errors_006()
{
	double exponent=2;	
	double ans;
	ans=pow(pow_related_errors_006_func_001(),exponent); /*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;

}

/*
* Types of defects: Errors related to power functions
* Complexity: Usage of an element in the structure which returns a very high value causing the result to overflow
*/

typedef struct
{
	double arr[1];
}pow_related_errors_007_s;

void pow_related_errors_007()
{
	double exponent=2;
	double ans;
	double ans1;
	pow_related_errors_007_s* newarr = (pow_related_errors_007_s *)malloc(sizeof(pow_related_errors_007_s));
	pow_related_errors_007_s* ptr_newarr =(pow_related_errors_007_s *)malloc(sizeof(pow_related_errors_007_s));

	newarr->arr[0]=10^3800;
	ptr_newarr->arr[0]=10^3800;

	 ans=pow(newarr->arr[0],exponent);
	 ans1=pow(ptr_newarr->arr[0],newarr->arr[0]);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
	free(newarr);
	free(ptr_newarr);
        dsink = ans + ans1;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Large positive base and exponent greater than 1
*/

void pow_related_errors_008()
{
	double base=10^3700;
	double exponent=2;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: When the base is negative and the exponent is negative
*/

void pow_related_errors_009()
{
	double base=-0.0000000000000000000000000000000000036;
	double exponent=-2;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small base and exponent greater than 1
*/

void pow_related_errors_010()
{
	double base=0.0000000000000000000000000000000000036;
	double exponent=20000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small base and exponent greater than 1
*/

void pow_related_errors_011()
{
	double base=-0.0000000000000000000000000000000000036;
	double exponent=20000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small base and even exponent greater than 1
*/

void pow_related_errors_012()
{
	double base=-0.0000000000000000000000000000000000036;
	double exponent=20000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and odd exponent greater than 1
*/

void pow_related_errors_013()
{
	double base=-0.0000000000000000000000000000000000036;
	double exponent=2000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small base and odd exponent greater than 1
*/

void pow_related_errors_014()
{
	double base=0.0000000000000000000000000000000000036;
	double exponent=21000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very large negative base and odd exponent greater than 1
*/

void pow_related_errors_015()
{
	double base=-10^3600;
	double exponent=21;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very large positive base and odd exponent greater than 1
*/

void pow_related_errors_016()
{
	double base=10^36;
	double exponent=20000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very large positive base and very small negative exponent
*/

void pow_related_errors_017()
{
	double base=10^36;
	double exponent=-10^36;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and very small negative exponent
*/

void pow_related_errors_018()
{
	double base=-10^36;
	double exponent=-10^36;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small positive base and very small negative exponent
*/

void pow_related_errors_019()
{
	double base=0.0004;
	double exponent=-10^3600;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and very small negative exponent
*/

void pow_related_errors_020()
{
	double base=-0.0004;
	double exponent=-10^3600;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Positive base and very small odd negative exponent
*/

void pow_related_errors_021()
{
	double base=100;
	double exponent=-10^3500;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and very small odd negative exponent
*/

void pow_related_errors_022()
{
	double base=-100;
	double exponent=-10^35000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small positive base and very small odd negative exponent
*/

void pow_related_errors_023()
{
	double base=0.0004;
	double exponent=-10^35000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and very small odd negative exponent
*/

void pow_related_errors_024()
{
	double base=-0.0004;
	double exponent=-10^35000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very small negative base and very small odd negative exponent
*/

void pow_related_errors_025()
{
	double base=10^3300;
	double exponent=0.000004;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Large base and large exponent together can lead to overflow
*/

void pow_related_errors_026()
{
	double base=10^10;
	double exponent=7000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Small base and large odd exponent together can lead to underflow
*/

void pow_related_errors_027()
{
	double base=-100^10;
	double exponent=7000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Small base and very small negative exponent together can lead to overflow
*/

void pow_related_errors_028()
{
	double base=-10^10;
	double exponent=-7100;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: Very Small negative base and very small exponent together can lead to underflow
*/

void pow_related_errors_029()
{
	double base=-10^30;
	double exponent=-10^3000;

	double ans;
	ans=pow(base,exponent);/*Tool should detect this line as error*/ /*ERROR:Data Overflow*/
        dsink = ans;
}

/*
* Types of defects: Errors related to power functions
* Complexity: power function main
*/
extern volatile int vflag;
void pow_related_errors_main ()
{
	if (vflag ==1 || vflag ==888)
	{
		pow_related_errors_001();
	}

	if (vflag ==2 || vflag ==888)
	{
		pow_related_errors_002();
	}

	if (vflag ==3 || vflag ==888)
	{
		pow_related_errors_003();
	}

	if (vflag ==4 || vflag ==888)
	{
		pow_related_errors_004();
	}

	if (vflag ==5 || vflag ==888)
	{
		pow_related_errors_005();
	}

	if (vflag ==6 || vflag ==888)
	{
		pow_related_errors_006();
	}

	if (vflag ==7 || vflag ==888)
	{
		pow_related_errors_007();
	}

	if (vflag ==8 || vflag ==888)
	{
		pow_related_errors_008();
	}

	if (vflag ==9 || vflag ==888)
	{
		pow_related_errors_009();
	}

	if (vflag ==10 || vflag ==888)
	{
		pow_related_errors_010();
	}

	if (vflag ==11 || vflag ==888)
	{
		pow_related_errors_011();
	}

	if (vflag ==12 || vflag ==888)
	{
		pow_related_errors_012();
	}

	if (vflag ==13 || vflag ==888)
	{
		pow_related_errors_013();
	}

	if (vflag ==14 || vflag ==888)
	{
		pow_related_errors_014();
	}

	if (vflag ==15 || vflag ==888)
	{
		pow_related_errors_015();
	}

	if (vflag ==16 || vflag ==888)
	{
		pow_related_errors_016();
	}

	if (vflag ==17 || vflag ==888)
	{
		pow_related_errors_017();
	}

	if (vflag ==18 || vflag ==888)
	{
		pow_related_errors_018();
	}

	if (vflag ==19 || vflag ==888)
	{
		pow_related_errors_019();
	}

	if (vflag ==20 || vflag ==888)
	{
		pow_related_errors_020();
	}

	if (vflag ==21 || vflag ==888)
	{
		pow_related_errors_021();
	}

	if (vflag ==22 || vflag ==888)
	{
		pow_related_errors_022();
	}

	if (vflag ==23 || vflag ==888)
	{
		pow_related_errors_023();
	}

	if (vflag ==24 || vflag ==888)
	{
		pow_related_errors_024();
	}

	if (vflag ==25 || vflag ==888)
	{
		pow_related_errors_025();
	}

	if (vflag ==26 || vflag ==888)
	{
		pow_related_errors_026();
	}

	if (vflag ==27 || vflag ==888)
	{
		pow_related_errors_027();
	}

	if (vflag ==28 || vflag ==888)
	{
		pow_related_errors_028();
	}

	if (vflag ==29 || vflag ==888)
	{
		pow_related_errors_029();
	}

}
