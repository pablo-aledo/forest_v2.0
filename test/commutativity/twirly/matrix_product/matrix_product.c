
#include <stdio.h>
#include <stddef.h>

int main() {
  const size_t N = 2;
  const size_t K = 3;
  const size_t M = 2;
  unsigned A[N][K] = {{3, 5, 15}, {99, 11, 33}};
  unsigned B[K][M] = {{4, 19}, {15, 8}, {32, 89}};
  unsigned C[N][M] = {0};

  for (size_t i = 0; i < N; ++i)
    for (size_t j = 0; j < M; ++j)
      for (size_t k = 0; k < K; ++k)
        C[i][j] += A[i][k] * B[k][j];

  fprintf(stderr, "%u\n", C[1][1]);

  return 0;
}
