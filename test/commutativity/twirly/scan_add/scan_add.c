
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned int input[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const size_t N = sizeof(input) / sizeof(unsigned int);
  unsigned int output[N] = {0};

  output[0] = input[0];

  for (size_t i = 1; i < N; ++i)
    output[i] = input[i] + output[i - 1];

  fprintf(stderr, "%u\n", output[N / 2]);

  return 0;
}
