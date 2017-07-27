
main() {
	int x;
	int *p = &x;

	while(x<10) {
		(*p)++;
	}                       
	return 0;
}

