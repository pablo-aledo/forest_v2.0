
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(array) / sizeof(unsigned int);

  for (size_t i = 0; i < N; ++i)
    array[i] = i;

  fprintf(stderr, "%u\n", array[N / 2]);

  return 0;
}
