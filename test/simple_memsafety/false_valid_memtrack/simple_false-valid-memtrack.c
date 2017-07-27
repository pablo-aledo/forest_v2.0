extern void __VERIFIER_error() __attribute__ ((__noreturn__));

#include <stdlib.h>

int *a, *b;
int n;

#define BLOCK_SIZE 10

void foo ()
{
  int i;
  for (i = 0; i < n; i++)
    a[i] = -1;
  for (i = 0; i < BLOCK_SIZE - 1; i++)
    b[i] = -1;
}

int main ()
{
  n = BLOCK_SIZE;
  a = malloc (n * sizeof(*a));
  b = malloc (n * sizeof(*b));
  *b++ = 0;
  foo ();
  if (*b)
  { free(a); free(b); } /* invalid free */
  else
  { free(a); free(b-1); }
  return 0;
}
