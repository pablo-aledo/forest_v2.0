int gcd(int x1, int x2, int x3, int x4, int x5, int x6, int x7, int x8){

X1:
	if(x1) goto X2; else goto X3;
X2:
	if(x2) return 1; else goto X3;
X3:
	if(x3) goto X4; else goto X5;
X4:
	if(x4) return 1; else goto X5;
X5:
	if(x5) goto X6; else goto X7;
X6:
	if(x6) return 1; else goto X7;
X7:
	if(x7) goto X8; else return 0;
X8:
	if(x8) return 1; else return 0;

}

int main() {
}
