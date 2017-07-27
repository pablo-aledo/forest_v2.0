/*
 * =====================================================================================
 * /
 * |     Filename:  variable.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/14/2014 04:22:58 AM
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

#include "variable.h"

Variable::Variable(){
	
	name_hint = "";
	type = "";
	real_value = "";
	is_propagated_constant = 0;
	isempty = 0;
	comes_from_non_annotated = 0;
	first_address = 0;
	last_address = 0;
	outofbounds = false;
	freed = true;
}

Variable::~Variable(){
	
}

