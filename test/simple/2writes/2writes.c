

int main(void) {
	int conds = 0;
	int x, y;

	y = x * 3;

	if( y == 6 )
		conds ++;

	y = x + 2;
	
	if( y == 4 )
		conds ++;

	if( conds == 2 )
		return 1;
	else
		return 0;

}
