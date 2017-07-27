

int main(void) {

	int numbers[3];
	int arraysize = 3;

	int i, j, temp;

	for (i = (arraysize - 1); i > 0; i--) {

		for (j = 1; j <= i; j++) {

			if (numbers[j-1] > numbers[j]) {

				temp = numbers[j-1];
				numbers[j-1] = numbers[j];
				numbers[j] = temp;

			}
		}
	}
}
