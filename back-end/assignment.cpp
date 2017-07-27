/*
 * =====================================================================================
 * /
 * |     Filename:  assignment.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/22/2014 07:24:50 PM
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


#include "assignment.h"

Assignment::Assignment(){
	
}

Assignment::~Assignment(){
	
}


Assignment::Assignment(string _operation, string _dst, string _op1, string _op2, string _basic_block){

	operation   = _operation;
	dst         = _dst;
	op1         = _op1;
	op2         = _op2;
	basic_block = _basic_block;

}

Assignment::Assignment( string _dst, string _src, string _basic_block){
	operation = "=";
	dst = _dst;
	op1 = _src;
	basic_block = _basic_block;


}

string Assignment::get_operation(){
	return operation;
}

string Assignment::get_dst(){
	return dst;
}


string Assignment::get_op1(){
	return op1;
}


string Assignment::get_op2(){
	return op2;
}

string Assignment::get_src(){
	return op1;
}



