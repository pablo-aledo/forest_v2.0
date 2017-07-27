/*
 * =====================================================================================
 * /
 * |     Filename:  getopt.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/20/2013 03:10:42 PM
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


#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>

#define NO_ARG		0
#define REQUIRED_ARG    1
#define OPTIONAL_ARG	2

/* static variables */
static int optwhere = 0;

/* types */

typedef struct getopt_data
{
	char *optarg;
	int optind, opterr, optopt, optwhere;
} getopt_data;


typedef enum GETOPT_ORDERING_T
{
	PERMUTE,
	RETURN_IN_ORDER,
	REQUIRE_ORDER
} GETOPT_ORDERING_T;

  struct option

  {
    char *name;			/* the name of the long option */
    int has_arg;		/* one of the above macros */
    int *flag;			/* determines if getopt_long() returns a
				 * value for a long option; if it is
				 * non-NULL, 0 is returned as a function
				 * value and the value of val is stored in
				 * the area pointed to by flag.  Otherwise,
				 * val is returned. */
    int val;			/* determines the value to return if flag is
				 * NULL. */

  };


char *strchr(const char *s, int c) {
	while (*s != (char) c) {
		if (!*s++) {
			return NULL;
		}
	}
	return (char *)s;
}

/*int memcmp(const void* buf1,*/
		/*const void* buf2,*/
		/*size_t count)*/
/*{*/
	/*if(!count)*/
		/*return(0);*/

	/*while(--count && *(char*)buf1 == *(char*)buf2 ) {*/
		/*buf1 = (char*)buf1 + 1;*/
		/*buf2 = (char*)buf2 + 1;*/
	/*}*/

	/*return(*((unsigned char*)buf1) - *((unsigned char*)buf2));*/
/*}*/

int memcmp(const char *cs, const char *ct, size_t n)
{
  size_t i;   

  for (i = 0; i < n; i++, cs++, ct++)
  {
    if (*cs < *ct)
    {
      return -1;
    }
    else if (*cs > *ct)
    {
      return 1;
    }
    else
    {
      return 0;
    }
  }
} 




/* write_globals: write the values into the globals from a getopt_data
   structure */
static void
write_globals (struct getopt_data *data)
{
  optarg = data->optarg;
  optind = data->optind;
  opterr = data->opterr;
  optopt = data->optopt;
  optwhere = data->optwhere;
}




/* reverse_argv_elements:  reverses num elements starting at argv */
	static void
reverse_argv_elements (char **argv, int num)
{
	int i;
	char *tmp;

	for (i = 0; i < (num >> 1); i++)
	{
		tmp = argv[i];
		argv[i] = argv[num - i - 1];
		argv[num - i - 1] = tmp;
	}
}





/* permute: swap two blocks of argv-elements given their lengths */
static void permute (char *const argv[], int len1, int len2) {
	reverse_argv_elements ((char **) argv, len1);
	reverse_argv_elements ((char **) argv, len1 + len2);
	reverse_argv_elements ((char **) argv, len2);
}

/* is_option: is this argv-element an option or the end of the option list? */
static int is_option (char *argv_element, int only) {
	return ((argv_element == 0) || (argv_element[0] == '-') || (only && argv_element[0] == '+'));
}


int strlen( char *str)
{
  const char *s;

  for (s = str; *s; ++s);
  return(s - str);
}

/*int strcmp(char *s1, char *s2)*/
/*{*/
    /*while((*s1 && *s2) && (*s1++ == *s2++));*/
    /*return *(--s1) - *(--s2);*/
/*}*/

int strcmp(char* s1, char* s2)
{
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(unsigned char*)s1-*(unsigned char*)s2;
}






/* getopt_internal:  the function that does all the dirty work */
	static int
getopt_internal (int argc, char *const argv[], const char *shortopts,
		const struct option *longopts, int *longind, int only,
		struct getopt_data *data)
{
	GETOPT_ORDERING_T ordering = PERMUTE;
	size_t permute_from = 0;
	int num_nonopts = 0;
	int optindex = 0;
	size_t match_chars = 0;
	char *possible_arg = 0;
	int longopt_match = -1;
	int has_arg = -1;
	char *cp = 0;
	int arg_next = 0;
	int initial_colon = 0;

	/* first, deal with silly parameters and easy stuff */
	if (argc == 0 || argv == 0 || (shortopts == 0 && longopts == 0)
			|| data->optind >= argc || argv[data->optind] == 0)
		return EOF;
	if (strcmp (argv[data->optind], "--") == 0)
	{
		data->optind++;
		return EOF;
	}

	/* if this is our first time through */
	if (data->optind == 0)
		data->optind = data->optwhere = 1;

	/* define ordering */
	if (shortopts != 0 && (*shortopts == '-' || *shortopts == '+'))
	{
		ordering = (*shortopts == '-') ? RETURN_IN_ORDER : REQUIRE_ORDER;
		shortopts++;
	}
	else
		ordering = (getenv ("POSIXLY_CORRECT") != 0) ? REQUIRE_ORDER : PERMUTE;

	/* check for initial colon in shortopts */
	if (shortopts != 0 && *shortopts == ':')
	{
		++shortopts;
		initial_colon = 1;
	}

	/*
	 * based on ordering, find our next option, if we're at the beginning of
	 * one
	 */
	if (data->optwhere == 1)
	{
		switch (ordering)
		{
			default:		/* shouldn't happen */
			case PERMUTE:
				permute_from = data->optind;
				num_nonopts = 0;
				while (!is_option (argv[data->optind], only))
				{
					data->optind++;
					num_nonopts++;
				}
				if (argv[data->optind] == 0)
				{
					/* no more options */
					data->optind = permute_from;
					return EOF;
				}
				else if (strcmp (argv[data->optind], "--") == 0)
				{
					/* no more options, but have to get `--' out of the way */
					permute (argv + permute_from, num_nonopts, 1);
					data->optind = permute_from + 1;
					return EOF;
				}
				break;
			case RETURN_IN_ORDER:
				if (!is_option (argv[data->optind], only))
				{
					data->optarg = argv[data->optind++];
					return (data->optopt = 1);
				}
				break;
			case REQUIRE_ORDER:
				if (!is_option (argv[data->optind], only))
					return EOF;
				break;
		}
	}
	/* we've got an option, so parse it */

	/* first, is it a long option? */
	if (longopts != 0
			&& (memcmp (argv[data->optind], "--", 2) == 0
				|| (only && argv[data->optind][0] == '+')) && data->optwhere == 1)
	{
		/* handle long options */
		if (memcmp (argv[data->optind], "--", 2) == 0)
			data->optwhere = 2;
		longopt_match = -1;
		possible_arg = strchr (argv[data->optind] + data->optwhere, '=');
		if (possible_arg == 0)
		{
			/* no =, so next argv might be arg */
			match_chars = strlen (argv[data->optind]);
			possible_arg = argv[data->optind] + match_chars;
			match_chars = match_chars - data->optwhere;
		}
		else
			match_chars = (possible_arg - argv[data->optind]) - data->optwhere;
		for (optindex = 0; longopts[optindex].name != 0; ++optindex)
		{
			if (memcmp
					(argv[data->optind] + data->optwhere, longopts[optindex].name,
					 match_chars) == 0)
			{
				/* do we have an exact match? */
				if (match_chars == (int) (strlen (longopts[optindex].name)))
				{
					longopt_match = optindex;
					break;
				}
				/* do any characters match? */
				else
				{
					if (longopt_match < 0)
						longopt_match = optindex;
					else
					{
						/* we have ambiguous options */
						if (data->opterr)
							fprintf (stderr, "%s: option `%s' is ambiguous "
									"(could be `--%s' or `--%s')\n",
									argv[0],
									argv[data->optind],
									longopts[longopt_match].name,
									longopts[optindex].name);
						return (data->optopt = '?');
					}
				}
			}
		}
		if (longopt_match >= 0)
			has_arg = longopts[longopt_match].has_arg;
	}

	/* if we didn't find a long option, is it a short option? */
	if (longopt_match < 0 && shortopts != 0)
	{
		cp = strchr (shortopts, argv[data->optind][data->optwhere]);
		if (cp == 0)
		{
			/* couldn't find option in shortopts */
			if (data->opterr)
				fprintf (stderr,
						"%s: invalid option -- `-%c'\n",
						argv[0], argv[data->optind][data->optwhere]);
			data->optwhere++;
			if (argv[data->optind][data->optwhere] == '\0')
			{
				data->optind++;
				data->optwhere = 1;
			}
			return (data->optopt = '?');
		}
		has_arg = ((cp[1] == ':')
				? ((cp[2] == ':') ? OPTIONAL_ARG : REQUIRED_ARG) : NO_ARG);
		possible_arg = argv[data->optind] + data->optwhere + 1;
		data->optopt = *cp;
	}

	/* get argument and reset data->optwhere */
	arg_next = 0;
	switch (has_arg)
	{
		case OPTIONAL_ARG:
			if (*possible_arg == '=')
				possible_arg++;
			data->optarg = (*possible_arg != '\0') ? possible_arg : 0;
			data->optwhere = 1;
			break;
		case REQUIRED_ARG:
			if (*possible_arg == '=')
				possible_arg++;
			if (*possible_arg != '\0')
			{
				data->optarg = possible_arg;
				data->optwhere = 1;
			}
			else if (data->optind + 1 >= argc)
			{
				if (data->opterr)
				{
					fprintf (stderr, "%s: argument required for option `", argv[0]);
					if (longopt_match >= 0)
					{
						fprintf (stderr, "--%s'\n", longopts[longopt_match].name);
						data->optopt = initial_colon ? ':' : '\?';
					}
					else
					{
						fprintf (stderr, "-%c'\n", *cp);
						data->optopt = *cp;
					}
				}
				data->optind++;
				return initial_colon ? ':' : '\?';
			}
			else
			{
				data->optarg = argv[data->optind + 1];
				arg_next = 1;
				data->optwhere = 1;
			}
			break;
		default:			/* shouldn't happen */
		case NO_ARG:
			if (longopt_match < 0)
			{
				data->optwhere++;
				if (argv[data->optind][data->optwhere] == '\0')
					data->optwhere = 1;
			}
			else
				data->optwhere = 1;
			data->optarg = 0;
			break;
	}

	/* do we have to permute or otherwise modify data->optind? */
	if (ordering == PERMUTE && data->optwhere == 1 && num_nonopts != 0)
	{
		permute (argv + permute_from, num_nonopts, 1 + arg_next);
		data->optind = permute_from + 1 + arg_next;
	}
	else if (data->optwhere == 1)
		data->optind = data->optind + 1 + arg_next;

	/* finally return */
	if (longopt_match >= 0)
	{
		if (longind != 0)
			*longind = longopt_match;
		if (longopts[longopt_match].flag != 0)
		{
			*(longopts[longopt_match].flag) = longopts[longopt_match].val;
			return 0;
		}
		else
			return longopts[longopt_match].val;
	}
	else
		return data->optopt;
}






/* read_globals: read the values from the globals into a getopt_data 
   structure */
	static void
read_globals (struct getopt_data *data)
{
	data->optarg = optarg;
	data->optind = optind;
	data->opterr = opterr;
	data->optopt = optopt;
	data->optwhere = optwhere;
}



int getopt (int argc, char *const argv[], const char *optstring) {
  struct getopt_data data;
  int r;

  read_globals (&data);
  r = getopt_internal (argc, argv, optstring, 0, 0, 0, &data);
  write_globals (&data);
  return r;
}

int main(int argc, char *argv[]) {


	int flags, opt;
	int nsecs, tfnd;

	nsecs = 0;
	tfnd = 0;
	flags = 0;
	while ((opt = getopt(argc, argv, "nt:")) != -1) {
		switch (opt) {
			case 'n':
				flags = 1;
				break;
			case 't':
				nsecs = atoi(optarg);
				tfnd = 1;
				break;
			default: /* '?' */
				fprintf(stderr, "Usage: %s [-t nsecs] [-n] name\n",
						argv[0]);
				exit(EXIT_FAILURE);
		}
	}

	printf("flags=%d; tfnd=%d; optind=%d\n", flags, tfnd, optind);

	return 0;
}
