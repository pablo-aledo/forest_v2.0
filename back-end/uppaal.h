/*
 * =====================================================================================
 * /
 * |     Filename:  uppaal.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/12/2014 11:51:36 AM
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

#ifndef _UPPAAL_H_
#define _UPPAAL_H_

#include <string>
#include <stdio.h>
#include <map>
#include "operators.h"
#include "options.h"
#include "solver_wrapper.h"
#include "utils.h"

using namespace std;


typedef struct UppaalVar{ 

	string name;
	string type;
	string init;

} UppaalVar;

inline bool operator<(const UppaalVar& lhs, const UppaalVar& rhs) {
	return lhs.name < rhs.name ;
}



class Uppaal {
public:
	void call_id(char* _call_id);
	void EndFn();
	void BeginFn(char* _fn_name);
	void add_eq_set(set<pair <string, int> > idx_val);
	void assign_global(string src, string dst);
	void assign_instruction(string src, string dst, string fn_name );
	void binary_instruction(string dst, string op1, string op2, string operation);
	void end_sim();
	void br_instr_cond(string cmp, bool invert);
	void mutex_unlock(char* name);
	void mutex_lock(char* name);
	Uppaal ();
	virtual ~Uppaal ();

private:
	vector<string> function_stack;
	string call_stack();
	string uppaal_index_condition(set<pair<string, int> > idx_comb);
	map<set<pair<string, int> >, int> last_idx_val;
	bool multiedge;
	map<string, int> bb_counter;
	string uppaal_function(string name);
	string and_cond( set<pair<string,int> > idx_val);
	string sem_name(string name);
	string uppaal_name(string name);
	void add_variable_to_table(string name, string type, string init);
	bool is_cmp(string operation);
	string content(string name);
	map<string, string> filter_uppaal_vars(map<string, string> input);
	string invert_condition(string cond);
	string concat(map<string, string> _assigns_map);
	map<string, string> last_operation;

	string prev_bb;
	map<string, string> assigns_map;
	string condition_pre;
	string sem_pre;
	string lockunlock_pre;
	string comparison;
	set<UppaalVar> variables;
	string call_id_m;
	
};

#endif /* end of include guard: _UPPAAL_H_ */
