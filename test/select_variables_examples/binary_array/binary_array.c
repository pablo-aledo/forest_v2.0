void __VERIFIER_assert(int val);

int main () {
	int a[8] = {0,0,0,0,1,1,1,1};
	int b[8] = {0,0,1,1,0,0,1,1};
	int c[8] = {0,1,0,1,0,1,0,1};
	int f[8] = {0,1,1,1,0,1,0,0};
	for(int i = 0; i < 8; ++i){
		int zg_1 = a[i] & b[i];
		int zg_2 = b[i] | c[i];
		int res  = zg_1 ^ zg_2;
		__VERIFIER_assert(res == f[i]);
	}
}

