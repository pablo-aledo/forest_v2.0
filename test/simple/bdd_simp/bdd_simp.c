int gcd(int x1, int x2, int x3){

X1:
	if(x1) goto X2; else goto X3;
X2:
	if(x2) return 0; else goto X3;
X3:
	if(x3) return 0; else return 1;

}

int main() {
}
