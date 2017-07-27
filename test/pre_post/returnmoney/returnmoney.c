/*
 * =====================================================================================
 * /
 * |     Filename:  returnmoney.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/02/2015 06:13:25 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#define N 5

void sort(int*, int){;}

int pickMaxCoin(int amount, int coins[], int n){
	for ( unsigned int i = 0; i < n; i++) {
		if(amount >= n) return n;
	}
	return 1;
}

void returnmoney(int given_money, int amount){
	int return_money = given_money-amount;
	int p_coins[N];// = {200, 100, 50, 25, 10};
	sort(p_coins, N);
	do {
		int coin = pickMaxCoin(return_money, p_coins, N);
		return_money -= coin;
	} while( return_money > 0 );
}

int main() {

	int given_money, amount;
	if(given_money-amount > 10) return 0;
	if(given_money-amount <  0) return 0;
	returnmoney(given_money, amount);
	return 0;
}

