/*
 * =====================================================================================
 * /
 * |     Filename:  assignment.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/22/2014 07:24:30 PM
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


#ifndef _ASSIGNMENT_H_
#define _ASSIGNMENT_H_

#include <string>

using namespace std;

class Assignment {
public:
	string get_src();
	string get_op2();
	string get_op1();
	string get_dst();
	string get_operation();
	Assignment(string operation, string dst, string op1, string op2, string basic_block);
	Assignment(string dst, string src, string basic_block);
	Assignment ();
	virtual ~Assignment ();


private:
	string operation;
	string dst;
	string op1;
	string op2;
	string basic_block;
	
};

#endif /* end of include guard: _ASSIGNMENT_H_ */
