/*
 * =====================================================================================
 * /
 * |     Filename:  solver_wrapper.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:44:33 PM
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

#ifndef _SOLVER_WRAPPER_H_
#define _SOLVER_WRAPPER_H_

#include <stdio.h>
#include <string>
#include <string.h>
#include <set>
#include <map>
#include <vector>
#include "variable.h"


using namespace std;


typedef struct NameAndPosition {
	string name;
	string position;
	string value;
} NameAndPosition;


inline bool operator<(const NameAndPosition& lhs, const NameAndPosition& rhs)
{
  return lhs.position > rhs.position;
}

class  SolverWrapper{
public:
	void set_freed(string name_mem, bool value);
	bool get_freed(string name_mem);
	void set_malloc_origin(string name, string malloc_origin);
	bool has_free_variables();
	void show_assigns();
	void set_assigning_globals(bool value);
	void initialize_real_value(string varname, string varhint);
	void load_file_initializations();
	void dump_file_initializations(string filename);

	SolverWrapper ();
	virtual ~SolverWrapper ();

	string get_position(string name);
	set<NameAndPosition> get_free_variables();
	vector<bool> get_path_stack();
	string gettype(string name);
	float get_solve_time();
	string realvalue(string varname);
	string get_first_content_value(string var);
	string get_comma_stack_conditions_static();
	string get_path_stack_str();
	string realvalue_mangled(string varname);
	map<string, Variable> get_map_variables();
	void set_outofbounds(string varname, bool outofbounds = true);
	bool get_outofbounds(string varname);
	bool is_forced_free_hint(string hint);
	void load_forced_free_hints();
	void insert_forced_free_var(string name);
	void assign_instruction(string src, string dst, string fn_name = "") ;
	void push_condition(string name, string actual_function, vector<string> joints, bool invert);
	bool get_comes_from_non_annotated(string name);
	void set_comes_from_non_annotated(string name);
	int get_last_address(string name);
	int get_first_address(string name);
	void free_var(string name);
	bool get_is_propagated_constant(string varname);
	void set_name_hint(string name, string hint);
	void settype(string name, string type);
	void push_path_stack(bool step);
	void print_path_stack();
	void insert_variable(string name, string position);
	bool is_constant(string varname);
	void set_is_propagated_constant(string varname);
	void unset_is_propagated_constant(string varname);
	void set_real_value(string varname, string value, string fn_name );
	void set_real_value(string varname, string value );
	void set_last_address(string name, int last_address);
	void set_first_address(string name, int first_address);
	void load_forced_free_vars();
	string get_type(string name);
	void get_context(SolverWrapper* other);
	void set_isdriver();
	void binary_instruction(string dst, string op1, string op2, string operation);
	string get_name_hint(string name);
	void cast_instruction(string src, string dst, string type_src, string type_dst, string sext);

	virtual bool solvable_problem() = 0;
	virtual void sym_store(string src, string addr) = 0;
	virtual void sym_load(string dst, string idx_content) = 0;
	virtual void push_condition_static_var(string cond, bool invert) = 0;
	virtual void load_state() = 0;
	virtual void save_state() = 0;
	virtual void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base) = 0;
	virtual string debug_content( string name ) = 0;
	virtual void set_sat(bool) = 0;
	virtual int show_problem() = 0;
	virtual void set_offset_tree( string varname, string tree ) = 0;
	virtual void solve_problem() = 0;
	virtual void cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext) = 0;
	virtual void bool_to_int8(string src, string dst) = 0;
	virtual void bool_to_int32(string src, string dst) = 0;
	virtual void push_condition_var(string name, bool invert = false ) = 0;
	virtual void assign_instruction_content(string src, string dst, string fn_name = "") = 0;
	virtual string eval(string expr) = 0;
	virtual string internal_condition(string condition) = 0;
	virtual void binary_instruction_content(string dst, string op1, string op2, string operation) = 0;
	virtual string internal_representation(int in, string type) = 0;
	virtual map<set<pair<string, int> > , int > get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address) = 0;
	virtual void clear_variable(string var) = 0;
	virtual void save_first_content(string var, string dst) = 0;
	virtual void variable_store(string src,string idx_content, int first_address, int last_address ) = 0;
	virtual string canonical_representation(string in) = 0;
	virtual string content_smt(string name) = 0;
	virtual void propagate_unary_extra(string src, string dst, bool forcedfree) = 0;
	virtual void propagate_binary_extra(string op1, string op2, string dst) = 0;
	virtual void add_neq_zero(string var) = 0;
	virtual void add_eq_zero(string var) = 0;
	virtual void add_bt(string var, string val) = 0;
	virtual void add_lt(string var, string val) = 0;
	virtual void add_smt(string smt) = 0;
	virtual void dump_conditions(stringstream& sstream) = 0;
	virtual void dump_model() = 0;
	virtual map<set<pair<string, int> >, int> get_map_idx_val(string name) = 0;
	virtual void add_eq_set(set<pair <string, int> > set_idx_val) = 0;
	virtual void set_content(string name, string value) = 0;
	virtual pair<int, int> get_range(string name) = 0;
	virtual bool empty_assertions() = 0;
	string find_by_name_hint(string hint);
	//void insert_variable_and_type(string var, string type);
	
	
protected:

	bool assigning_globals;
	map<string, string> initializations;
	set<string> forced_free_hints;
	map<string, Variable> variables_generic;
	set<NameAndPosition> free_variables;
	bool isdriver;
	float spent_time;
	set<string> already_forced_free;
	map<string, string> stacks;
	vector<string> flatened_conditions;
	set<string> flatened_variables;
	vector<string> conditions_static;
	set<string> forced_free_vars;
	map<string, string> first_content_value;
	vector<bool> path_stack;
	bool debug;

	int minval(string type);
	int maxval(string type);
	vector<int> jump_offsets(string offset_tree);
	set<set<pair<string, int> > > get_exclusions( map<set<pair<string, int> > , int > solutions );
	void check_name_and_pos(string name, string position);
	string z3_type(string type);
	bool is_free_var(string name);
	void add_indexes(string dst, vector<string> indexes);
	string get_idx_type(string idx_content );
	void load_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val);
	void add_range_index(string dst, map<set<pair<string, int> > , int > map_idx_val );
	string negateop(string predicate);
	bool need_for_dump(string name, string content);
	void set_real_value_hint(string hint, string value );
	void propagate_unary(string src, string dst, bool forcedfree);
	void propagate_binary(string op1, string op2, string dst);
	void set_first_content_value(string var, string value);
	void show_variables();
	void show_concurrency_constraints();
	void show_check_sat();
	void show_header();
	void show_tail();
	string extract_condition(string content);
	string get_last_condition(string name);
	string actual(string name);
	string past(string name);
	string name_without_suffix(string name);
	void dump_flatened_variables(FILE* file = stdout );
	void dump_flatened_conditions(FILE* file = stdout );
	bool check_name(string name);
	bool check_unmangled_name(string name);
	string name( string input, string fn_name = "" );
	string get_offset_tree( string varname );
	set<string> unlock_points(string mutex);
	string or_unlocking(string condition, string mutex);
	string or_paths(string dest);
	string and_stores(string sync_point);
	string stack(string sync_point);
	void set_real_value_mangled(string varname, string value );
	int get_num_fvars();
	bool implemented_operation(string operation);
	string wired_and( string op1, string op2, int nbits );
	string wired_xor( string op1, string op2, int nbits );
	string find_mem_of_id(string id);
	void get_context_back(SolverWrapper* other);
	void initialize_var(string name);
	void store_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val);
	void push_condition(string cond, bool invert = false );
	void dump_variable(string name, string type, FILE* file);
	string get_sized_type(string name);
	void solver_insert_sync_point(string lockunlock, string sync_name, string mutex_name);
	//string find_by_name_hint(string hint);
	void setcontent(string varname, string content);
	bool is_forced_free(string position, bool colateral_effect = true);

};

#endif /* end of include guard: _SOLVER_H_ */

