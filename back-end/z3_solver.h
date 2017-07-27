/*
 * =====================================================================================
 * /
 * |     Filename:  solver.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:46 PM
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


#ifndef _SOLVER_H_
#define _SOLVER_H_

#include "solver_wrapper.h"
#include "z3_variable.h"




typedef struct Condition {
	string cond;
	string function;
	set<string> joints;
} Condition;






class Z3Solver : public SolverWrapper {
public:

	virtual string eval(string expression) = 0;
	void add_eq_set(set<pair <string, int> > set_idx_val);
	map<set<pair <string, int> >, int> get_map_idx_val(string name);
	void dump_check_sat(FILE* file);
	void dump_model();
	void dump_conditions(stringstream& sstream);
	void set_content(string name, string value);
	pair<int, int> get_range(string name);
	bool empty_assertions();


	virtual void get_name(string& filename) = 0;
	void push_condition_var(string name, bool invert = false );
	void bool_to_int8(string src, string dst);
	void bool_to_int32(string src, string dst);
	int show_problem();
	void load_state();
	void save_state();
	void store_idx_vals(string src, map<set<pair<string, int> > , int > map_idx_val);
	void sym_load(string dst, string addr);
	void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base);
	void add_range_index(string dst, map<set<pair<string, int> > , int > map_idx_val );
	string get_offset_tree( string varname );
	void propagate_binary_extra(string op1, string op2, string dst);
	void setcontent(string varname, string content);
	string content( string name );
	string debug_content( string name );
	void load_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val);
	void sym_store(string src, string addr);
	string get_idx_type(string addr);
	void add_indexes(string dst, vector<string> indexes);
	void set_offset_tree( string varname, string tree );
	void init_indexes(string dst, string op1, string op2 = "");
	void propagate_unary_extra(string src, string dst, bool forcedfree);
	void binary_instruction_content(string dst, string op1, string op2, string operation);
	void assign_instruction_content(string src, string dst, string fn_name = "");
	Z3Solver ();
	virtual ~Z3Solver ();
	void solve_problem();
	virtual void dump_variables(FILE* file) = 0;
	string z3_type(string type);
	virtual string canonical_representation(string in) = 0;
	virtual void cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext);
	string content_smt(string name);
	void push_condition_static_var(string name, bool invert);
	void variable_store(string src, string idx_content, int first_address, int last_address );
	void clear_variable(string var);
	void save_first_content(string var, string dst);
	bool solvable_problem();
	void set_sat(bool _sat);
	void add_eq_zero(string variable);
	void add_neq_zero(string variable);
	void add_bt(string var, string val);
	void add_lt(string var, string val);
	void add_smt(string smt);
	string get_anded_stack_conditions();

protected:
	string flat_function_stack();
	bool is_cond_sign(string cond);
	string get_comma_stack_conditions();
	void set_non_linear(string var);
	virtual bool islinear(string varname) = 0;
	bool proplinear;
	bool check_representable();

	vector<bool> path_stack_save;
	vector<string> conditions_static_save;
	vector<Z3Variable> conditions_save;

	vector<Z3Variable> conditions;
	string result_get(string get_str);
	bool get_is_sat(string is_sat);
	bool sat;
	map<string, string> first_content;
	string negation(string condition);
	map<string, Z3Variable> variables;
	void remv_op_constant(string& condition);
	virtual string internal_condition(string condition) = 0;
	virtual void dump_problem(string& filename) = 0;
	virtual string internal_representation(int in, string type) = 0;
	virtual void dump_extra(FILE* file) = 0;
	virtual void dump_header(FILE* file) = 0;

	void div_operation(string op1, string op2, string dst, stringstream& content_ss);
	void mul_operation(string op1, string op2, string dst, stringstream& content_ss);
	void sub_operation(string op1, string op2, string dst, stringstream& content_ss);
	void add_operation(string op1, string op2, string dst, stringstream& content_ss);
	void xor_operation(string op1, string op2, string dst, stringstream& content_ss);
	void or_operation(string op1, string op2, string dst, stringstream& content_ss);
	void and_operation(string op1, string op2, string dst, stringstream& content_ss);
	void eq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void bt_operation(string op1, string op2, string dst, stringstream& content_ss);
	void lt_operation(string op1, string op2, string dst, stringstream& content_ss);
	void geq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void uleq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void ugt_operation(string op1, string op2, string dst, stringstream& content_ss);
	void ugeq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void ult_operation(string op1, string op2, string dst, stringstream& content_ss);
	void leq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void rem_operator(string op1, string op2, string dst, stringstream& content_ss);
	void neq_operation(string op1, string op2, string dst, stringstream& content_ss);
	void right_shift(string op1, string op2, string dst, stringstream& content_ss);
	void left_shift(string op1, string op2, string dst, stringstream& content_ss);




	bool need_for_dump(string name, string content);
	void dump_tail(FILE* file);
	void dump_get(FILE* file);
	void dump_conditions(FILE* file);
	
};

#endif /* end of include guard: _SOLVER_H_ */
