
int time = 0;

int main() {  
	int a,b;
	int t;  
	while (b != 0) {  
		t = b;  
		b = a % b;  
		a = t;  
		time += 5;
	}  
	return a;  
} 
