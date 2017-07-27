/*
 * =====================================================================================
 * /
 * |     Filename:  linear_bblast.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/11/2014 02:25:15 AM
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


#ifndef _LINEAR_BBLAST_H_
#define _LINEAR_BBLAST_H_

#include "linear_solver.h"
#include <sstream>
#include "utils.h"
#include "linear_variable_bb.h"

class LinearBblast : public SolverWrapper{
public:
	string eval(string expression);
	void add_eq_set(set<pair <string, int> > set_idx_val);
	LinearBblast();
	~LinearBblast();

	void dump_conditions(stringstream& sstream);
	void dump_model();
	map<set<pair <string, int> >, int> get_map_idx_val(string name);
	void set_content(string name, string value);
	pair<int, int> get_range(string name);
	bool empty_assertions();

protected:

	string bv_polarity(string polarity);
	string type_of_free_var(string nameandposition);
	string adapt_width(string name, string type_free_var, string type_dst);
	string get_rep_type(string varname);
	string biggest_type(string type1, string type2);
	void set_non_linear(string var);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_check_sat(FILE* file);
	string smt2_representation(LinearVarBb variable);
	string z3_type(string type);
	void dump_header(FILE* file);
	bool islinear(string varname);
	bool check_linearity();
	void equalize(LinearVariable& variable);
	LinearVariable bigger(LinearVariable variable);
	LinearVariable smaller(LinearVariable variable);
	vector<LinearVariable> get_tail(vector<LinearVariable> vect);
	void get_convex_constraints_rec( vector<LinearVariable> linear_variables, vector<vector<LinearVariable> >* ret, int n_ret );
	vector<vector<LinearVariable> > get_convex_constraints( vector<LinearVariable> linear_variables );
	LinearVarBb negate_var(LinearVarBb variable);
	string negateop_linear(string predicate);
	bool need_for_dump(string name, map<string,HexNum> content);
	void dump_constraints(FILE* file);
	void dump_free_variables(FILE* file);
	void dump_aux_variables(FILE* file);
	bool is_empty(string name);
	map<string, HexNum> content(string name);
	string result_get(string a);

	void div_operation(string op1, string op2, string dst);
	void mul_operation(string op1, string op2, string dst);
	void sub_operation(string op1, string op2, string dst);
	void add_operation(string op1, string op2, string dst);
	void xor_operation(string op1, string op2, string dst);
	void eq_operation(string op1, string op2, string dst);
	void bt_operation(string op1, string op2, string dst);
	void lt_operation(string op1, string op2, string dst);
	void geq_operation(string op1, string op2, string dst);
	void uleq_operation(string op1, string op2, string dst);
	void ugt_operation(string op1, string op2, string dst);
	void ugeq_operation(string op1, string op2, string dst);
	void ult_operation(string op1, string op2, string dst);
	void leq_operation(string op1, string op2, string dst);
	void rem_operator(string op1, string op2, string dst);
	void neq_operation(string op1, string op2, string dst);
	void right_shift(string op1, string op2, string dst);
	void left_shift(string op1, string op2, string dst);


	vector<bool> path_stack_save;
	vector<string> conditions_static_save;
	vector<LinearVarBb> conditions_save;
	bool proplinear;
	int n_problems;
	map<string, LinearVarBb> first_content;
	vector<LinearVarBb> conditions;
	bool sat;
	map<string, LinearVarBb > variables;
	vector<AuxVar> aux_vars;




	virtual int show_problem();
	virtual void dump_statistics(FILE* file);
	virtual void get_name(string& filename);
	virtual string type_free_var(string name_hint);
	virtual void dump_problem(string filename);
	virtual void or_operation(string op1, string op2, string dst);
	virtual void and_operation(string op1, string op2, string dst);


	bool solvable_problem();
	void sym_store(string src, string addr);
	void sym_load(string dst, string idx_content);
	void push_condition_static_var(string cond, bool invert);
	void load_state();
	void save_state();
	void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base);
	string debug_content( string name );
	void set_sat(bool);
	void set_offset_tree( string varname, string tree );
	void solve_problem();
	void cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext);
	void bool_to_int8(string src, string dst);
	void bool_to_int32(string src, string dst);
	void push_condition_var(string name, bool invert = false );
	void assign_instruction_content(string src, string dst, string fn_name = "");
	string internal_condition(string condition);
	void binary_instruction_content(string dst, string op1, string op2, string operation);
	string internal_representation(int in, string type);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);
	void clear_variable(string var);
	void save_first_content(string var, string dst);
	void variable_store(string src,string idx_content, int first_address, int last_address );
	string canonical_representation(string in);
	string content_smt(string name);
	void propagate_unary_extra(string src, string dst, bool forcedfree);
	void propagate_binary_extra(string op1, string op2, string dst);
	void add_eq_zero(string variable);
	void add_neq_zero(string variable);
	void add_bt(string var, string val);
	void add_lt(string var, string val);
	void add_smt(string smt);


};

#endif /* end of include guard: _LINEAR_BBLAST_H_ */
