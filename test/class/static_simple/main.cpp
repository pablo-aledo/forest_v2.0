class Simple {
public:
  static int calc (int a, int b){
    return a+b;
  }
};

int main () {
  int a;
  int b;
  if(Simple::calc(a, b) > 5){
    return 1;
  } else {
    return 0;
  }
}
