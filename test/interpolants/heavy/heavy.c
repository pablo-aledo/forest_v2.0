/* Licensed under the GPLv2 */

#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 

int main()
{
	char array[2 * 2] = {1};


#ifdef KLEE
  klee_make_symbolic(&array, sizeof(array), "array");
#endif

	unsigned int a = 1, i, j, k;

	for (i = 0; i < sizeof(array); i++)
		for (j = 0; j < sizeof(array); j++)
			for (k = 0; k < sizeof(array); k++)
				array[i] = array[j] + array[k];

	if (a != 0)
		goto ERROR;

	return array[100];
ERROR:
	return 1;
}
