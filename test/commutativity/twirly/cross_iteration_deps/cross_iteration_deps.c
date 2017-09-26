int main() {
  unsigned int array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const int N = sizeof(array) / sizeof(unsigned int);

  for (int i = 1; i < N; ++i)
    array[i] += array[i - 1];

  return 0;
}
