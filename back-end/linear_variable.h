/*
 * =====================================================================================
 * /
 * |     Filename:  linear_variable.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/14/2014 04:48:21 AM
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


#ifndef _LINEAR_VARIABLE_H_
#define _LINEAR_VARIABLE_H_

#include <map>
#include <string>

using namespace std;

class LinearVariable  {
public:
	LinearVariable ();
	~LinearVariable ();

	map<string, float> content;
	string polarity;
	bool islinear;

};

#endif /* end of include guard: _LINEAR_VARIABLE_H_ */

