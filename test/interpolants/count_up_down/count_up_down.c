
int main() {
	int n;

	if(n < 0) return 1;

	int x=n, y=0;
	while(x>0) {
		x--;
		y++;
	}

	if(y!=n) return 0; // target (impossible bug)
	else return 1;
}
