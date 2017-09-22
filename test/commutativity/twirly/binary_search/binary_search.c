
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 11, 15, 33, 67, 99};
  const size_t N = sizeof(array) / sizeof(unsigned int);
  size_t L = 0, U = N - 1, M = 0;
  unsigned T = 33;

  while (L <= U) {
    M = (L + U) / 2;
    if (array[M] == T)
      break;
    if (array[M] < T)
      L = M + 1;
    else
      U = M - 1;
  }

  fprintf(stderr, "%zu\n", M);
  fprintf(stderr, "%u\n", array[N / 2]);

  return 0;
}
