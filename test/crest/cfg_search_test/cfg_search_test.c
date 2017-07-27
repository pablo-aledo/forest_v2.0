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


int data[200];

int main(void) {
  bool goal = 0;
  unsigned char c;

  for (int i = 0; i < 200; i++) {
    data[i] = 400;
  }
  data[100] = 13;

  for (int i = 0; i < 200; i++) {
    // Data match?
    if (c == data[i]) {
      goal = 1;
    }

    // Useless zero check.
    int a;
    if (a == 0) { }
  }

  return 0;
}
