/*
 * =====================================================================================
 * /
 * |     Filename:  mixed_bblast.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/13/2014 04:03:59 PM
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

#ifndef _MIXED_BBLAST_H_
#define _MIXED_BBLAST_H_


#include "solver_wrapper.h"
#include "linear_variable_bb.h"
#include "linear_bblast.h"
#include "utils.h"
#include <stdlib.h>

typedef struct BoolVar {
	string name;
	string type;
} BoolVar;


class  MixedBblast: public LinearBblast {
public:
	MixedBblast();
	virtual ~MixedBblast();
	int show_problem();
	void dump_model();

protected:
	void dump_statistics(FILE* file);
	void get_name(string& filename);
	string type_free_var(string name_hint);
	void and_operation(string op1, string op2, string dst);
	void or_operation(string op1, string op2, string dst);
	void dump_problem(string filename);
	void dump_bit_operations(FILE* file);
	void dump_bits(FILE* file);
	vector<BoolVar> bits;
	vector<string> bit_conditions;

};



#endif /* end of include guard: _MIXED_BBLAST_H_ */
