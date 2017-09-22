
void test() {
  int i = 10;
  int a = 0;

  while (--i) {
    a++;

    if(a == 5)
      break;

    a++;
  }
}
