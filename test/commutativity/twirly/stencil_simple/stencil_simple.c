int main() {
  unsigned input[] = {14, 75, 66, 67, 64, 74, 44, 31};
  const int N = sizeof(input) / sizeof(unsigned);
  unsigned output[N] = {0};

  for (int i = 1; i < N - 1; ++i)
    output[i] = input[i - 1] - 2 * input[i] + input[i + 1];

  return 0;
}
