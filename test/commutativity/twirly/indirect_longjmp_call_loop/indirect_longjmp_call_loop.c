
#include <setjmp.h>
#include <stdio.h>

jmp_buf jump_buffer;

void test(int count) {
  longjmp(jump_buffer, count + 1);
}

int main() {
  volatile int count = 0; // local variables must be volatile for setjmp
  int i = 0;

  while (i < 10) {
    count = 0;
    i++;
    if (setjmp(jump_buffer) != 9) {
      test(count++); // setjump() will return count+1
    }
  }

  return 0;
}
