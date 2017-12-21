
class Simple {
public:
   Simple (int a, int b){
    m_val =  a + b;
  }

  int get_val () const {
    return m_val;
  }

private:
  int m_val;
};

int main () {
  int a;
  int b;
  Simple c(a ,b);
  
  if (c.get_val () > 6){
    return 0;
  } else {
    return 1;
  }
}
