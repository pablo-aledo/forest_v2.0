
int main() {
	int a, b;

	/*if(a >  92) return 0;*/
	/*if(b >  92) return 0;*/
	/*if(a <   0) return 0;*/
	/*if(b <   0) return 0;*/

	if( a == 0 || b == 0 ) return 0;

	while(true){
		a = a%b;
		if(a==0){
			return b;
		}
		b = b%a;
		if(b==0){
			return a;
		}
	}
}
