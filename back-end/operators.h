/*
 * =====================================================================================
 * /
 * |     Filename:  operators.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:20:13 PM
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

#ifndef _OPERATORS_H_
#define _OPERATORS_H_ 


#include <stdio.h>
#include <string>
#include <map>
#include <sstream>
#include <vector>
#include <set>
#include <unistd.h>
#include <stdlib.h>
#include <assert.h>

using namespace std;








class Operators {
public:
	void set_alloca_pointer(int _alloca_pointer);
	int get_alloca_pointer();
	string flat_function_stack();
	vector<string> get_functions_and_bbs_trace();
	void checkerror_bb(char* name);
	void checkerror_fn(char* name);
	void assume(char* _assumption_register);
	void assertion(char* _assertion_register);
	void memcpy(char* a, char* b, char* c, char* d, char* e);
	void pointer_ranges();
	string get_actual_bb();
	Operators ();
	virtual ~Operators ();

	void binary_op(char*, char*, char*, char*);
	void cast_instruction(char*, char*, char*, char*);
	void load_instr(char*, char*);
	void store_instr(char*, char*);
	void store_instr_2(char* _src, char* _addr);
	void load_instr_2(char* _dst, char* _addr);
	void cmp_instr(char*, char*, char*, char*);
	bool br_instr_cond(char*, char*);
	void br_instr_incond();
	void begin_bb(char* a);
	void end_bb(char* a);
	void alloca_instr(char* a, char* b);
	void begin_sim();
	void end_sim();
	void getelementptr(char*, char*, char*, char*);
	void global_var_init(char* _name,char* _type, char* _value);
	void Free_fn( char* _fn_name );
	void NonAnnotatedCallInstr( char* _fn_name, char* _ret_type );
	void ReturnInstr(char* _retname );
	void CallInstr( char* _oplist, char* _ret_to );
	void CallInstr_post( char* _fn_name, char* _ret_type, char* _caller );
	void BeginFn(char* _fn_name, char* fn_oplist);
	void select_op(char* dest, char* cond, char* sel1, char* sel2 );
	string get_actual_function();
	string name( string input, string fn_name = "" );
	vector<string> name( vector<string> input, string fn_name = "" );
	bool check_mangled_name(string name);
	string get_file_initializations();
	void* fp_hook(char* _register_name);

private:
	string crcstack();
	string crcstack_name(string);
	void fork_on_array(string dst);
	void push_function_and_bb(string function_and_bb);
	vector<string> functions_and_bbs;


	map<string, int> first_addresses;
	map<string, int> last_addresses;
	map<string, int> nonannotated_call_count;
	vector<string> oplist_gl;
	string ret_to_gl;
	string ret_gl;
	int callstack_size;

	bool is_variable_pointer(string addr);
	string get_index_expr(string offset_tree, vector<string> indexes, string base);
	bool all_constant(vector<string> names);
	void pr_callstack();
	bool see_each_problem;

	int alloca_pointer;
	vector<pair<string, string> > callstack;

	string actual_function;
	string actual_bb;

	bool propagate_constants;
	bool exit_on_insert;
	//map<string, string> map_pos_to_last_store;
	int get_offset(vector<string> indexes, string offset_tree, string* remaining_tree);

	
	string get_type(string name);
	void set_name_hint(string name, string hint);
	void set_offset_tree( string varname, string tree );
	void push_path_stack(bool step);
	void print_path_stack();
	string realvalue(string varname);
	bool debug;

	string file_initializations;
};




#endif /* end of include guard: _OPERATORS_H_ */

