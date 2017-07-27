/*
 * =====================================================================================
 * /
 * |     Filename:  z3_realint.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/07/2014 09:55:48 AM
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

#ifndef _Z3_REALINT_H_
#define _Z3_REALINT_H_

#include "z3_solver.h"

class Z3RealInt : virtual public Z3Solver{
public:
	Z3RealInt();
	virtual ~Z3RealInt();

	string eval(string expression);
	void dump_variables(FILE* file);
	void dump_header(FILE* file);

	string internal_condition(string condition);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);
	string internal_representation(int in, string type);
	string canonical_representation(string in);
	void get_name(string& filename);

protected:
	bool islinear(string varname);
	void dump_bits(FILE* file);
	set<string> bits;
	string and_non_constant(string op1, string op2, int width, string uniq_id);
	string or_non_constant(string op1, string op2, int width, string uniq_id);
	void change_cast(string& condition);
	void get_operands(string condition, string operation, string& substr, string& before, string& after, string& param);
	void get_operands(string condition, string operation, string& substr, string& before, string& after, string& param1, string& param2);
	void representation_constants(string& condition);
	void replace_bv_casts(string& condition);
	void replace_bv_ints(string& condition);
	void replace_xor(string& condition);
	void replace_and(string& condition);
	void replace_or(string& condition);
	string and_constant(string op1, string op2);
	void replace_right_shift(string& condition);
	void replace_left_shift(string& condition);
	void dump_problem(string& filename_base);
	string or_constant(string op1, string op2);
	string complement_op(string op1);
	void dump_extra(FILE* file);
	void dump_type_limits(FILE* file);
	
};


#endif /* end of include guard: _Z3_REALINT_H_ */
