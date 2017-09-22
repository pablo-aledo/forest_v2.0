
int test(int k) {
  int i = 100;
  int a = 0;

  while (--i) {
    a++;

    if(a == 50)
      return k + 1;

    a++;
  }

  return k - 1;
}
