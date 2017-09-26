int main() {
  char *array[] = {"ab", "cd", "ef", "gh"};
  const int N = sizeof(array) / sizeof(char *);
  const int n = strlen(array[0]);
  char acc[N * 2 + 1] = {0};

  for (int i = 0; i < N; ++i)
    strncpy(acc + i * n, array[i], n);

  return 0;
}
