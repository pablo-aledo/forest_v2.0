/*
 * =====================================================================================
 * /
 * |     Filename:  state.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/22/2014 07:41:02 PM
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


#ifndef _STATE_H_
#define _STATE_H_

#include "assignment.h"
#include <vector>

using namespace std;

class State {
public:
	State ();
	State (vector<Assignment> assignments, string condition, string bb);
	virtual ~State ();

	vector<Assignment> get_assignments();
	string get_condition();
	string get_bb();

private:

	vector<Assignment> assignments;
	string condition;
	string bb;


	
};

#endif /* end of include guard: _STATE_H_ */
