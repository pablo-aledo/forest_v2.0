/*
 * =====================================================================================
 * /
 * |     Filename:  z3_variable.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/14/2014 04:41:28 AM
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

#include "z3_variable.h"

Z3Variable::Z3Variable(){
	content = "";
	tree = "";
	islinear = true;
	
}

Z3Variable::~Z3Variable(){
	
}

