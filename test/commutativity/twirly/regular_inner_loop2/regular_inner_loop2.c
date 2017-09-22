
void test() {
  int i = 10;
  int j = 0;
  int a = 0;

  while (--i) {
    for(j = 0; j < 10; j++)
      a++;

    for(; j < 20; j++)
      a += 5;
  }
}
