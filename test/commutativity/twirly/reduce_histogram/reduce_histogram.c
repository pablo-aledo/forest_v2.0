
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(array) / sizeof(unsigned);
  const size_t K = 3;
  unsigned bins[K] = {0};

  for (size_t i = 0; i < N; ++i)
    bins[array[i] % K] += array[i];

  fprintf(stderr, "%u\n", bins[K / 2]);

  return 0;
}
