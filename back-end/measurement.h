/*
 * =====================================================================================
 * /
 * |     Filename:  measurement.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 09:24:49 AM
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

#ifndef _MEASUREMENT_H_
#define _MEASUREMENT_H_

#include <stdio.h>
#include <set>
#include <string>
#include <vector>
#include <sstream>
#include <string.h>
#include <assert.h>
#include <fstream>
#include <iostream>
#include <map>

using namespace std;

class Measurement {
public:
	Measurement ();
	virtual ~Measurement ();

	/**
	 * @brief  Begin basic Block
	 *
	 * @param name: Name of the basic block
	 */
	void begin_bb(char* a);

	/**
	 * @brief End basic block
	 *
	 * @param name
	 */
	void end_bb(char* a);

	/**
	 * @brief Function that is called at the begining of simulation
	 */
	void begin_sim_measurement(char*, char*);

	/**
	 * @brief Function that is called at the end of simulation
	 */
	void end_sim();

	void BeginFn(char* _fn_name);
	void EndFn();

	void br_instr_cond_measurement(bool value);

	int vector_int(char*);
	float vector_float(char* _name);
	char vector_char(char*);
	long vector_long(char* _name);
	short vector_short(char*);


	void br_count();
	void end_count();
	map<string, vector<string> > load_test_vectors();

private:

	set<string> visited_bbs;
	set<string> visited_fns;
	set<string> available_fns;
	set<string> available_bbs;
	map<string, vector<string> > test_vectors;
	vector<string> fn_stack;
	vector<bool> path_stack;
	string actual_fn_name;
	int branches_count;
	
};









#endif /* end of include guard: _OPERATORS_H_ */

