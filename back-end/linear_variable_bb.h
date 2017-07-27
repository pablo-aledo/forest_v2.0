/*
 * =====================================================================================
 * /
 * |     Filename:  linear_variable_bb.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/11/2014 03:12:30 AM
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


#ifndef _LINEAR_VARIABLE_BB_H_
#define _LINEAR_VARIABLE_BB_H_

#include <stdio.h>
#include <map>
#include <string>
#include <assert.h>
#include "utils.h"

using namespace std;


class HexNum {
public:
	HexNum ();
	HexNum (int val, string type);
	HexNum (int val);
	virtual ~HexNum ();

        HexNum operator+(const HexNum& other);
        HexNum operator-(const HexNum& other);
        HexNum operator*(const HexNum& other);
        HexNum operator/(const HexNum& other);
        HexNum operator*(const int& other);
        HexNum operator/(const int& other);
        bool   operator==(const HexNum& other);
	const char* c_str(string type);
	int int_value;
private:
};


class LinearVarBb {
public:
	LinearVarBb ();
	virtual ~LinearVarBb ();
	bool islinear;
	map<string, HexNum> content;
	string polarity;
	string type_rep;

private:

	
};


class AuxVar {
	public:
		string name;
		string type;
};


#endif /* end of include guard: _LINEAR_VARIABLE_BB_H_ */
