/*
 * =====================================================================================
 * /
 * |     Filename:  linear_variable_bb.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/11/2014 03:11:59 AM
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

#include "linear_variable_bb.h"
#include "/media/disk/release/back-end/architecture.h"


LinearVarBb::LinearVarBb(){
	islinear = true;
}

LinearVarBb::~LinearVarBb(){
	
}

HexNum::HexNum (){
	int_value = 0;
}
HexNum::HexNum (int val){

	int_value = val;

}
HexNum::~HexNum (){}

HexNum HexNum::operator+(const HexNum& other){
	return HexNum(int_value+other.int_value);
}
HexNum HexNum::operator-(const HexNum& other){
	return HexNum(int_value-other.int_value);
}
HexNum HexNum::operator*(const HexNum& other){
	return HexNum(int_value*other.int_value);
}
HexNum HexNum::operator/(const HexNum& other){
	return HexNum(int_value/other.int_value);
}
HexNum HexNum::operator*(const int& other){
	return HexNum(int_value*other);
}
HexNum HexNum::operator/(const int& other){
	return HexNum(int_value/other);
}
bool   HexNum::operator==(const HexNum& other){
	return int_value == other.int_value;
}
const char*  HexNum::c_str(string type){
	string ret = tokenize(hex_representation_2(int_value, type), "#x")[0];
	int bytes = bits(type)/4;

	if(ret.length() > bytes){
		ret = ret.substr(ret.length() - bytes);
	}

	if(ret.length() < bytes){
		char lastbyte = ret[0];
		if(lastbyte == '8' || lastbyte == '9' || lastbyte == 'a' || lastbyte == 'b' || lastbyte == 'c' || lastbyte == 'd' || lastbyte == 'e' || lastbyte == 'f'){
			lastbyte = 'f';
		} else {
			lastbyte = '0';
		}
		for ( unsigned int i = ret.length(); i < bytes; i++) {
			ret = lastbyte + ret;
		}
		
	}
	
	assert(ret.length() == bytes && "Representation of different length than especified");

	ret = "#x" + ret;

	return ret.c_str();
}
