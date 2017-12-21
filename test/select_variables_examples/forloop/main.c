void __VERIFIER_assert(int val);

int main () {
	int a = 1;
	int b = 2;
	int c;

	for (int i = 0; i < 10; ++i){
		c = a + b;
	}

	__VERIFIER_assert(c == 4);

}

