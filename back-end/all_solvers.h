/*
 * =====================================================================================
 * /
 * |     Filename:  all_solvers.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/07/2014 04:24:08 PM
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

#include "linear_solver.h"
#include "z3_bitvector.h"
#include "z3_realint.h"
#include "polynomic_solver.h"
#include "mixed_int.h"
#include "mixed_bblast.h"
#include "linear_bblast.h"


class AllSolvers : public SolverWrapper {


public:
	void add_eq_set(set<pair <string, int> > set_idx_val);
	map<set<pair <string, int> >, int> get_map_idx_val(string name);
	AllSolvers ();
	virtual ~AllSolvers ();


	string eval(string expr);
	void assign_instruction_content(string src, string dst, string fn_name = "");
	string internal_condition(string condition);
	void binary_instruction_content(string dst, string op1, string op2, string operation);
	void solve_problem();
	string internal_representation(int in, string type);
	void cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext);
	map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address);
	void clear_variable(string var);
	void save_first_content(string var, string dst);
	void sym_store(string src, string addr);
	void sym_load(string dst, string idx_content);
	void push_condition_static_var(string cond, bool invert);
	void load_state();
	void save_state();
	void variable_store(string src,string idx_content, int first_address, int last_address );
	void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base);
	string debug_content( string name );
	void set_sat(bool);
	int show_problem();
	bool solvable_problem();
	void set_offset_tree( string varname, string tree );
	string canonical_representation(string in);
	void bool_to_int8(string src, string dst);
	void bool_to_int32(string src, string dst);
	string content_smt(string name);
	void push_condition_var(string name, bool invert = false );
	void propagate_unary_extra(string src, string dst, bool forcedfree);
	void propagate_binary_extra(string op1, string op2, string dst);
	void add_eq_zero(string variable);
	void add_neq_zero(string variable);
	void add_bt(string var, string val);
	void add_lt(string var, string val);
	void add_smt(string smt);
	void dump_conditions(stringstream& sstream);
	void dump_model();
	void set_content(string name, string value);

	pair<int, int> get_range(string name);
	bool empty_assertions();

protected:


	vector<SolverWrapper*> solvers;
	SolverWrapper* driver;


};
