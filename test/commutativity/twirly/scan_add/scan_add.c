int main() {
  unsigned int input[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const int N = sizeof(input) / sizeof(unsigned int);
  unsigned int output[N] = {0};

  output[0] = input[0];

  for (int i = 1; i < N; ++i)
    output[i] = input[i] + output[i - 1];

  return 0;
}
