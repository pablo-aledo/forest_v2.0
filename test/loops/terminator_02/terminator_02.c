#include <stdio.h>

int main() {
	char x;
	char z;

	if(x>100) return 1;
	if(z>100) return 1;


	while(x<100 && 100<z) {
		bool tmp=printf("");
		if (tmp) {
			x++;
		}
		else {
			x--;
			z--;
		}
	}                       

	return 0;
}


