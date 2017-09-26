
int main() {
  int i = 100;
  int a = 0;

  while (--i) {
    a++;

    if(a == 50)
      return 0;

    a++;
  }
}
