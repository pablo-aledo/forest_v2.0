
#include <stdio.h>
#include <stddef.h>

int main() {
  const size_t N = 16;
  const unsigned max_iterations = 10;
  unsigned iterations[N] = {0};

  for (size_t x0 = 0; x0 < 4; ++x0)
    for (size_t y0 = 0; y0 < 4; ++y0) {
      unsigned iteration_count = 0;
      unsigned x = 0, y = 0;

      while (x * x + y * y < 4 && iteration_count < max_iterations) {
        unsigned x_tmp = x * x - y * y + x0;
        unsigned y = 2 * x * y + y0;
        x = x_tmp;
        iteration_count++;
      }

      iterations[x0 * 4 + y0] = iteration_count;
    }

  fprintf(stderr, "%u\n", iterations[N / 2]);

  return 0;
}
