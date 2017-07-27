
int x=0;

void eval(void) {
	while (1) {
		x=0;
		break;
	}
	return;
}


int main() {

	while(1) {
		eval();
		if(x != 0) return 1;
	}

	return 0;
}
