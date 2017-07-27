/*
 * =====================================================================================
 * /
 * |     Filename:  mixed_int.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/10/2014 10:34:26 AM
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

#ifndef _MIXED_INT_H_
#define _MIXED_INT_H_

#include "solver_wrapper.h"
#include "linear_variable.h"
#include "linear_solver.h"
#include "utils.h"
#include "architecture.h"
#include <stdlib.h>
#include "linear_variable_bb.h"

class  MixedInt: public LinearSolver {
public:
	MixedInt();
	virtual ~MixedInt ();
	int show_problem();

protected:
	void dump_aux_variables(FILE* file);
	void dump_statistics(FILE* file);
	void get_name(string& filename);
	void right_shift(string op1, string op2, string dst);
	bool islinear(string varname);
	string smt2_representation(LinearVariable variable);
	void dump_header(FILE* file);
	void and_operation(string op1, string op2, string dst);
	void or_operation(string op1, string op2, string dst);
	void dump_problem(string filename);
	void dump_bit_limits(FILE* file);
	void dump_bit_operations(FILE* file);
	void dump_bits(FILE* file);
	vector<string> bits;
	vector<string> bit_conditions;

	vector<AuxVar> aux_vars;
};


#endif /* end of include guard: _MIXED_INT_H_ */


