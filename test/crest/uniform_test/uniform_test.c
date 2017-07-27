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
#ifdef KLEE 
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif 


int main(void) {

	int a;
	int b;
	int c;
	int d;

#ifdef KLEE

	klee_make_symbolic(&a, sizeof(a), "main_register_a");
	klee_make_symbolic(&b, sizeof(b), "main_register_b");
	klee_make_symbolic(&c, sizeof(c), "main_register_c");
	klee_make_symbolic(&d, sizeof(d), "main_register_d");

#endif

	if (a == 5) {
		if (b == 19) {
			if (c == 7) {
				if (d == 4) {
					return 1;
				}
			}
		}
	}

	return 0;
}
