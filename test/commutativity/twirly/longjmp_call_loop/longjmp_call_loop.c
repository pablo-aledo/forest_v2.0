
#include <setjmp.h>
#include <stdio.h>

jmp_buf jump_buffer;

int main() {
  volatile int count = 0; // local variables must be volatile for setjmp
  int i = 0;

  while (i < 10) {
    count = 0;
    i++;
    if (setjmp(jump_buffer) != 9) {
      ++count;
      longjmp(jump_buffer, count); // setjump() will return count+1
    }
  }

  return 0;
}
