int main() {
  const int N = 2;
  const int K = 3;
  const int M = 2;
  unsigned A[N][K] = {{3, 5, 15}, {99, 11, 33}};
  unsigned B[K][M] = {{4, 19}, {15, 8}, {32, 89}};
  unsigned C[N][M] = {0};

  for (int i = 0; i < N; ++i)
    for (int j = 0; j < M; ++j)
      for (int k = 0; k < K; ++k)
        C[i][j] += A[i][k] * B[k][j];

  return 0;
}
