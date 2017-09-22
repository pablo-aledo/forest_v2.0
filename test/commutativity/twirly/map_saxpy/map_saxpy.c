
#include <stdio.h>
#include <stddef.h>

int main() {
  unsigned int X[] = {14, 75, 66, 67, 64, 74, 44, 31};
  unsigned int Y[] = {13, 41, 39, 12, 20, 70, 47};
  unsigned int a = 19;
  const size_t N = sizeof(X) / sizeof(unsigned int);

  for (size_t i = 0; i < N; ++i)
    Y[i] = a * X[i] + Y[i];

  fprintf(stderr, "%u\n", Y[N / 2]);

  return 0;
}
