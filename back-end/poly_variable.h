/*
 * =====================================================================================
 * /
 * |     Filename:  poly_variable.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/30/2014 12:35:39 PM
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

#ifndef _POLY_VARIABLE_
#define _POLY_VARIABLE_

#include <map>
#include <set>
#include <string>

using namespace std;

class PolyVariable  {
public:
	PolyVariable ();
	~PolyVariable ();

	map< set<string> , float> content;
	string polarity;
	bool islinear;

};

#endif /* end of include guard: _POLY_VARIABLE_ */
