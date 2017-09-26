
int main() {
  int i = 100;
  int j = 100;
  int a = 0;

  while (--i) {
    a++;

    while(--j) {
      if(a == 50)
        return 0;
    }

    a++;
  }
}
