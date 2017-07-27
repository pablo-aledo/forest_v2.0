/*
 * =====================================================================================
 * /
 * |     Filename:  2calls.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/19/2014 04:25:39 PM
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


int function(){
	int a;
	return a;
}

int main() {
	if(function()){
		if(function()){
			return 1;
		} else {
			return 2;
		}
	} else {
		return 3;
	}

}
