/*
 * =====================================================================================
 * /
 * |     Filename:  assert.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/06/2014 02:08:47 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#define __STRING(x)	#x
#   define __ASSERT_FUNCTION	((__const char *) 0)
# define __ASSERT_VOID_CAST (void)
# define assert(expr) \
  (__ASSERT_VOID_CAST ((expr) ? 0 :					      \
		       (__assert (__STRING(expr), __FILE__, __LINE__,    \
				       __ASSERT_FUNCTION), 0)))
#define attribute_noreturn __attribute__ ((__noreturn__))
char* __uclibc_progname = "assert";
extern "C" void attribute_noreturn __assert(const char *assertion, const char * filename,
			  int linenumber, register const char * function);

int main() {
	int a;
	assert(a != 0);
	return 0;
}
