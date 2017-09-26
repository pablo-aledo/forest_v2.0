int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const int N = sizeof(array) / sizeof(unsigned int);

  for (int i = 0; i < N; ++i)
    array[i] = i;

  return 0;
}
