
void potential_exit(int);

void test() {
  int i = 100;
  int a = 0;

  while (--i) {
    a++;

    if(a == 50)
      potential_exit(1);

    a++;
  }

  return;
}
