/*
 * =====================================================================================
 * /
 * |     Filename:  getopt_long.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/14/2014 11:52:03 AM
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

// Example from http://linuxprograms.wordpress.com/2012/06/22/c-get opt_long-example-accessing-command-line-arguments/


extern "C" int getopt_long(int argc, char * const argv[], const char *optstring, const struct option *longopts, int *longindex);

#define	no_argument		0
#define required_argument	1
#define optional_argument	2

struct option
{
  char *name;
  int has_arg;
  int *flag;
  int val;
};

int main() {

	static struct option long_options[] = {
		{"area",      no_argument,       0,  'a' },
		{"perimeter", no_argument,       0,  'p' },
		{"length",    required_argument, 0,  'l' },
		{"breadth",   required_argument, 0,  'b' },
		{0,           0,                 0,  0   }
	};

	char* str_1 = "#########";
	char* str_2 = "aaaaaaaaa";
	char* ar[2];
	ar[0] = str_1;
	ar[1] = str_2;



	int long_index = 0;
	if( getopt_long(2, ar,"apl:b:", long_options, &long_index ) == 'a' )
		return 1;
	else
		return 0;
}
