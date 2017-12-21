
class Add {
public:
  int calc (int a, int b){
    return a + b;
  }
};

int main () {
  Add a;
  int b;
  int c;
  if (a.calc(b, c) > 6){
    return 0;
  } else {
    return 1;
  }
}
