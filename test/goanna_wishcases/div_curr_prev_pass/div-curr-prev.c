#include <stdlib.h>

int main(){
  int curr = rand()%1000;
  int prev = rand()%1000;
  if(curr > prev){
    curr = 100 / (curr - prev);
  }
  return 0;
}
