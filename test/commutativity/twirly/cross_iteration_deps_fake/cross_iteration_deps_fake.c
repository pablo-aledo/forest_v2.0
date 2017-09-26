int main() {
  unsigned int array[] = {0};
  const int N = sizeof(array) / sizeof(unsigned int);

  for (int i = 1; i < N; ++i)
    array[i] += array[i - 1];

  return 0;
}
