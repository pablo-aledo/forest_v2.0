int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const int N = sizeof(array) / sizeof(unsigned);
  const int K = 3;
  unsigned bins[K] = {0};

  for (int i = 0; i < N; ++i)
    bins[array[i] % K] += array[i];

  return 0;
}
