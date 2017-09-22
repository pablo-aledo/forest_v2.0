
#include <stdio.h>
#include <string.h>
#include <stddef.h>

int main() {
  char *array[] = {"ab", "cd", "ef", "gh"};
  const size_t N = sizeof(array) / sizeof(char *);
  const size_t n = strlen(array[0]);
  char acc[N * 2 + 1] = {0};

  for (size_t i = 0; i < N; ++i)
    strncpy(acc + i * n, array[i], n);

  fprintf(stderr, "%s\n", acc);

  return 0;
}
