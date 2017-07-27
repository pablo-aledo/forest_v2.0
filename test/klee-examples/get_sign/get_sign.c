/*
 * First KLEE tutorial: testing a small function
 */
#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 



int getsign(int x) {
  if (x == 0)
     return 0;
  
  if (x < 0)
     return -1;
  else 
     return 1;
} 

int main() {
  int a;

#ifdef KLEE
  klee_make_symbolic(&a, sizeof(a), "a");
#endif
  return getsign(a);
} 
