
void test(void);
void bar(void);

int main(void) {
  int i = 100;

  while (--i) {
    test();
    bar();
  }
  return 0;
}
