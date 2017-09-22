
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned input[] = {14, 75, 66, 67, 64, 74, 44, 31};
  const size_t N = sizeof(input) / sizeof(unsigned);
  unsigned output[N] = {0};

  for (size_t i = 1; i < N - 1; ++i)
    output[i] = input[i - 1] - 2 * input[i] + input[i + 1];

  fprintf(stderr, "%u\n", output[N / 2]);

  return 0;
}
