
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(array) / sizeof(unsigned);
  unsigned acc = 0;

  for (size_t i = 0; i < N; ++i)
    acc += array[i];

  fprintf(stderr, "%u\n", acc);

  return 0;
}
