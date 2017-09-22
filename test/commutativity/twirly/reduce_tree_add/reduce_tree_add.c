
#include <stdio.h>
#include <string.h>
#include <stddef.h>

int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(array) / sizeof(unsigned);
  unsigned utility[N] = {0};
  size_t i = 0;
  size_t j = 0;
  size_t sz = N;

  memcpy(utility, array, N * sizeof(unsigned));

  while (sz > 1) {
    j = 0;
    for (i = 0; i < sz; i += 2)
      utility[j++] = utility[i] + utility[i + 1];
    sz = j;
  }

  fprintf(stderr, "%u\n", utility[0]);

  return 0;
}
