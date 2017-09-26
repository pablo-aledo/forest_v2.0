int main() {
  unsigned array[] = {3, 5, 15, 99, 11, 33, 5, 67};
  const int N = sizeof(array) / sizeof(unsigned int);
  unsigned T = 33;
  int i;

  for (i = 0; i < N; ++i)
    if (array[i] == T)
      break;

  return 0;
}
