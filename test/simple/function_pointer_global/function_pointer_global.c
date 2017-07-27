int cscreate(void *(*t)(void*)) {
	return 0;
}

void *thread1(void *csLOCALPARAMthread1arg) {
}

int main(void) {
	cscreate(thread1);
	return 0;
}
                                                       


