/*
 * =====================================================================================
 * /
 * |     Filename:  interpolant_solver.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/19/2014 04:58:56 AM
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

#ifndef _INTERPOLANT_SOLVER_H_
#define _INTERPOLANT_SOLVER_H_


#include "solver_wrapper.h"
#include "z3_realint.h"
#include <assert.h>
#include "utils.h"
#include "operators.h"
#include "assignment.h"
#include "state.h"
#include "database.h"
#include "automaton.h"
#include "options.h"


typedef struct Triple {
	string str1;
	string str2;
	string str3;
} Triple;




class InterpolantSolver : public SolverWrapper {
public:
	string eval(string expression);
	void add_eq_set(set<pair <string, int> > set_idx_val);

	map<set<pair <string, int> >, int> get_map_idx_val(string name);

	InterpolantSolver ();
	virtual ~InterpolantSolver ();

	bool solvable_problem();
	void sym_store(string src, string addr);
	void sym_load(string dst, string idx_content);
	void push_condition_static_var(string cond, bool invert);
	void load_state();
	void save_state();
	void pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base);
	string debug_content( string name );
	void set_sat(bool);
	int show_problem();
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
	void add_neq_zero(string var);
	void add_eq_zero(string var);
	void add_bt(string var, string val);
	void add_lt(string var, string val);
	void add_smt(string smt);
	void dump_conditions(stringstream& sstream);
	void dump_model();
	void set_content(string name, string value);

	pair<int, int> get_range(string name);
	bool empty_assertions();



private:
	void change_polarity(vector<Triple>& rejecting_automaton, string basic_block);
	bool check_inclusion(string interpolant_second, string interpolant_connected);
	int id_of(vector<string> bbs, string name);
	void generate_rejecting_automaton(vector<string> bbs,vector<string> conditions, vector<string> interpolants);
	void dump_get_interpolants(FILE* file);
	void dump_header(FILE* file);
	void dump_interpolants(FILE* file);
	void print_possible_tansitions(vector<set<string> > possible_transitions);
	bool is_valid_vector_states(vector<string> input);
	void print_possible_combinations(set<vector<string> > result );
	set<vector<string> > filter_combination_of_transitions( set<vector<string> > input);
	void get_combination_of_transitions( vector<set<string> > possible_transitions, set<vector<string> >& result, vector<string> actual );
	string negate_polarity(string predicate);
	string condition_of(string content, bool invert = 0);
	bool all_terminations_are_rejected(vector<vector<string> > rejecting_information);
	vector<string> rejecting_automaton_states( vector<Automaton> matrix_automaton );
	vector<string> get_states(vector<Automaton> vector_aut);
	void show_matrix_automatons(vector<vector<Automaton> > matrix_automaton);
	void rm_from_matrix(vector<Automaton> vector_aut, vector<vector<Automaton> > matrix_aut);
	bool is_in_matrix(vector<Automaton> vector_aut, vector<vector<Automaton> > matrix_aut);
	vector<vector<Automaton> > iterate_transitions( vector<Automaton> vector_automatons);
	vector<set<string> > get_possible_transitions(vector<Automaton> vector_automatons);
	void dump_check_sat(FILE* file);
	void dump_active_path_in_interpolant(string active_path, string interpolant, FILE* file);
	bool problem_in_interpolant_state();

	bool is_in_interpolant;
	void calculate_interpolants();

	Z3RealInt* z3solver;

	string name_of_dst(string name, bool side_effects = 1);
	string name_of_src(string name);
	string bb_name(string name, bool side_effects = 1);

	map<string, int> sequential_identifier;
	map<string, int> sequential_identifier_bbs;
	map<string, int> sequential_identifier_bbs_bak;

	vector<pair<string, string> > pairs_bb_condition;

	string last_dst;
	string last_dst_content;
	string last_bb;
	string last_condition;


	vector<Assignment> assignments;
	vector<State> states;

	bool is_cmp(string operation);

	string last_indicator;
	vector<string> stack_of_conditions;
	vector<string> stack_of_conditions_bak;

	Automaton program_automaton;
	vector<Automaton> rejecting_automatons;
	
	
};

#endif /* end of include guard: _INTERPOLANT_SOLVER_H_ */

