
#include <stdio.h>

int main() {
  int i = 0;

  while (i < 10) {
    fprintf(stderr, "count: %d\n", i);
    i++;
  }

  return 0;
}
