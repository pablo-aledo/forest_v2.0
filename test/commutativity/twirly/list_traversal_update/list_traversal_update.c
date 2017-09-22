
#include <stdio.h>

struct list {
  int i;
  struct list *next;
};

struct list *tail;
struct list *random;

struct list *list_construct(void) {
  static struct list buf[11];
  struct list *head = &buf[0];
  tail = &buf[10];
  random = &buf[4];

  buf[0].next = &buf[1];
  buf[1].next = &buf[2];
  buf[2].next = &buf[3];
  buf[3].next = &buf[4];
  buf[4].next = &buf[5];
  buf[5].next = &buf[6];
  buf[6].next = &buf[7];
  buf[7].next = &buf[8];
  buf[8].next = &buf[9];
  buf[9].next = &buf[10];
  buf[10].next = NULL;

  buf[0].i = 1;
  buf[1].i = 2;
  buf[2].i = 3;
  buf[3].i = 4;
  buf[4].i = 5;
  buf[5].i = 6;
  buf[6].i = 7;
  buf[7].i = 8;
  buf[8].i = 9;
  buf[9].i = 10;
  buf[10].i = 11;

  return head;
}

int main(int argc, const char *argv[]) {
  struct list *head = list_construct();
  struct list *p = NULL;
  int count = 0;

  p = head;
  while (p) {
    p->i++;
    p = p->next;
  }

  printf("%d\n", head->i);
  printf("%d\n", tail->i);
  printf("%d\n", random->i);

  return 0;
}
