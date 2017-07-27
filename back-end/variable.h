/*
 * =====================================================================================
 * /
 * |     Filename:  variable.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/14/2014 04:20:26 AM
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


#ifndef _VARIABLE_H_
#define _VARIABLE_H_



#include <map>
#include <set>
#include <string>

using namespace std;

class Variable {
public:
	Variable ();
	~Variable ();

	string name_hint;
	string type;
	string real_value;
	bool is_propagated_constant;
	bool isempty;
	bool comes_from_non_annotated;
	int first_address;
	int last_address;
	bool outofbounds;
	string malloc_origin;
	bool freed;

};



#endif /* end of include guard: _VARIABLE_H_ */
