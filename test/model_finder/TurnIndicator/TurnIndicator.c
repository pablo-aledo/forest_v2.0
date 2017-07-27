/*
 * =====================================================================================
 * /
 * |     Filename:  TurnIndicator.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/04/2014 02:09:23 PM
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




char tilOld;
char tilLevel;
char emerSwitch;
char ctr;
char lOld;
char rOld;
char left;
char right;
char left_p;
char right_p;
char lampsleft;
char lampsright;

void setTil(char l){
	tilLevel = l;
}

void switchEmerMode(){
	emerSwitch = (emerSwitch == 0);
}

void manageFlashing(){

	char left_p  = left;
	char right_p = right;

	switch(tilLevel){
		case 0: left = 1; right = 0; break;
		case 1: left = 0; right = 0; break;
		case 2: left = 0; right = 1; break;
	}

	if( !left_p  && left  ) ctr = 0;
	if( !right_p && right ) ctr = 0;

	tilOld = tilLevel;
}

void manageEmerMode(){

	char tilLevel_p = tilLevel;

	ctr = 3;

	if(tilOld == 1 && tilLevel_p != 1 && tilLevel == 2 )  right = 1;
	if(tilOld == 1 && tilLevel_p != 1 && tilLevel == 0 )  left  = 1;
	if(tilOld != 1 || tilLevel_p == 1){ left  = 1; right = 1; }

	tilOld = 1;

}

void FlashOn(){


	if(lOld  || left)  lampsleft  = 1;
	if(rOld  || right) lampsright = 1;
	if((unsigned) ctr < 3) ctr++;

}

void FlashOff(){

	lampsleft  = 0;
	lampsright = 0;


	if((unsigned)ctr >= 3){
		lOld = 0;
		rOld = 0;
	} 

}

int main(){
	manageFlashing();
}

