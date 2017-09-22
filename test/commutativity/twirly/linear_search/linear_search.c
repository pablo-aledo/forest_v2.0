
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(array) / sizeof(unsigned int);
  unsigned T = 33;
  size_t i;

  for (i = 0; i < N; ++i)
    if (array[i] == T)
      break;

  fprintf(stderr, "%zu\n", i);
  fprintf(stderr, "%u\n", array[N / 2]);

  return 0;
}
