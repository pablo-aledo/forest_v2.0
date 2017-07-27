/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency_backend.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/28/2015 03:21:57 PM
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


#ifndef _CONCURRENCY_BACKEND_H_
#define _CONCURRENCY_BACKEND_H_

#include <stdio.h>
#include "solver_wrapper.h"
#include "operators.h"
#include <set>
#include <map>
#include <string>
#include "utils.h"

using namespace std;

class Concurrency {
public:
	void end_sim();
	void callinstr(char* _oplist);
	void callinstr_post(char* _fn_name);
	Concurrency ();
	virtual ~Concurrency ();
	string oplist;

	set<string> current_functions;
	set<set<string> > concurrent_functions;
	map<int, string> map_functions;

private:
	int actual_id;



};

#endif /* end of include guard: _CONCURRENCY_BACKEND_H_ */
