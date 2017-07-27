/*
 * =====================================================================================
 * /
 * |     Filename:  z3_variable.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/14/2014 04:40:22 AM
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



#ifndef _Z3_VARIABLE_H_
#define _Z3_VARIABLE_H_

#include <string>
#include <map>
#include <set>

using namespace std;


class Z3Variable {
public:
	Z3Variable ();
	~Z3Variable ();

	bool islinear;

	string content;
	string tree;
	map<set<pair<string, int> > , int > idx_values;
	set<string> indexes;

};

#endif /* end of include guard: _Z3_VARIABLE_H_ */

