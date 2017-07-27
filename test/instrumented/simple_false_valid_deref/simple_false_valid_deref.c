extern "C" void rv_emit_async(const char *event, const char *format, ...);
extern "C" void* fr_malloc(unsigned long size);
extern "C" void  fr_free  (void* pointer);

int *a, *b;
int n;

#define BLOCK_SIZE 128

void foo ()
{
  int i;
  for (i = 0; i < n; i++)
    a[i] = -1;
  for (i = 0; i < BLOCK_SIZE - 1; i++)
    b[i] = -1;
}

int main ()
{
void * __1;
int __2;
int * __3;
int __4;
  n = BLOCK_SIZE;
  a = (int*)fr_malloc (n * sizeof(*a));
  b = (int*)(__1 = (fr_malloc ((__2 = (n), rv_emit_async("e02", "%d", __2), __2) * sizeof(*b))), rv_emit_async("e01", "%zd", __1), __1);
  *b++ = 0;
  foo ();
  if ((__3 = (b), rv_emit_async("e03", "%zd", __3), __3)[(__4 = (-2), rv_emit_async("e04", "%d", __4), __4)]) /* invalid deref */
  { fr_free(a); fr_free(b-1); }
  else
  { fr_free(a); fr_free(b-1); }

  return 0;
}
