/* Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
 *
 * This file is part of CREST, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 */


void f(int);
void g(int);
void h(int);
void i(int);
int result;

void f(int a) {
  if (a > 13) {
    result = 14;
  } else {
    result = 12;
  }
}

void g(int a) {
  h(a);

  if (a == 7) {
    result = 7;
  } else {
    result = 0;
  }

  i(a);
}

void h(int a) {
  if (a == -4) {
    result = -4;
  } else {
    result = -5;
  }
}

void i(int a) {
  if (a == 100) {
    result = 100;
  } else {
    result = 99;
  }
}

int main(void) {
  int a;

  if (a == 19) {
    result = 19;
  } else {
    result = 18;
  }

  f(a);

  g(a);

  if (a != 1) {
    result = -1;
  } else {
    result = 1;
  }

  return 0;
}
