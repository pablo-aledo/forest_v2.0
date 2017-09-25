int main() {
  unsigned int array[] = {0};
  const int N = sizeof(array) / sizeof(unsigned int);

  for (size_t i = 1; i < N; ++i)
    array[i] += array[i - 1];

  return 0;
}
