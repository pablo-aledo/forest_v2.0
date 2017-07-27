/*
 * =====================================================================================
 * /
 * |     Filename:  uppaal.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/12/2014 11:50:49 AM
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

#include "uppaal.h"
#include "database.h"

extern Operators* operators;
extern Database* database;
extern SolverWrapper* solver;
extern Options* options;

Uppaal::Uppaal(){

	prev_bb = uppaal_function(options->cmd_option_str("seedfn")) + "_" + "start";
	if(prev_bb.substr(0,1) == "_") prev_bb = prev_bb.substr(1);
	multiedge = 0;
	call_id_m = "";
	
}

Uppaal::~Uppaal(){
	
}

string Uppaal::uppaal_name(string name){
	string ret;
	if(solver->get_name_hint(name) == "") ret = name;
	else ret = solver->get_name_hint(name);

	myReplace(ret, "+", "_");
	return ret;
}

string Uppaal::uppaal_function(string name){

	string ret = name;
	myReplace(ret, "_", "");
	return ret;
}

string Uppaal::concat(map<string, string> _assigns_map){

	string ret;

	for( map<string,string>::iterator it = _assigns_map.begin(); it != _assigns_map.end(); it++ ){
		if(uppaal_name(it->first) != "" && it->second != "")
			ret += uppaal_name(it->first) + "=" + it->second + ",";
	}

	return ret;
	
}

string Uppaal::sem_name(string name){
	myReplace(name, "+", "");
	//if(name.substr(name.length()-2) == "_0") name = name.substr(0, name.length() - 2);
	return name;
}


string Uppaal::uppaal_index_condition(set<pair<string, int> > idx_comb){

	string ret;

	for( set<pair<string, int> >::iterator it = idx_comb.begin(); it != idx_comb.end(); it++ ){
		ret += " && " + it->first + " == " + itos(it->second) ;
	}

	ret = ret.substr(4);
	
	return ret;

}

void Uppaal::mutex_lock(char* _name){

	string name = string(_name);
	printf("\e[31m uppaal::mutex_lock \e[0m %s %lu\n", name.c_str(), solver->get_map_idx_val(operators->name(name)).size());

	string bb = call_stack() + operators->get_actual_bb(); if(bb.substr(0,1) == "_") bb = bb.substr(1);
	string lockunlock = lockunlock_pre;
	string assigns = concat(assigns_map);
	if(multiedge){
		for( map<set<pair<string, int> >, int>::iterator it = last_idx_val.begin(); it != last_idx_val.end(); it++ ){
			set<pair<string, int> > idx_comb = it->first;
			int value = it->second;
			string condition = uppaal_index_condition(idx_comb);
			string sem = sem_name(solver->get_name_hint("mem_" + itos(value)));
			database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
			add_variable_to_table(sem, "SemTyID", "");
		}
		
	} else {
		string condition = condition_pre;
		string sem = sem_pre;
		database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
		add_variable_to_table(sem, "SemTyID", "");
	}

	multiedge = solver->get_map_idx_val(operators->name(name)).size();

	prev_bb = bb;
	assigns_map.clear();
	last_operation.clear();
	lockunlock_pre = "lock";
	condition_pre = "";

	if(multiedge){
		last_idx_val = solver->get_map_idx_val(operators->name(name));
	} else {
		sem_pre = sem_name(solver->get_name_hint("mem_" + solver->realvalue(operators->name(name))));
	}

}


void Uppaal::mutex_unlock(char* _name){

	string name = string(_name);
	printf("\e[31m uppaal::mutex_unlock \e[0m %s\n", name.c_str());


	string bb = call_stack() + operators->get_actual_bb(); if(bb.substr(0,1) == "_") bb = bb.substr(1);
	string lockunlock = lockunlock_pre;
	string assigns = concat(assigns_map);
	if(multiedge){
		for( map<set<pair<string, int> >, int>::iterator it = last_idx_val.begin(); it != last_idx_val.end(); it++ ){
			set<pair<string, int> > idx_comb = it->first;
			int value = it->second;
			string condition = uppaal_index_condition(idx_comb);
			string sem = sem_name(solver->get_name_hint("mem_" + itos(value)));
			database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
			add_variable_to_table(sem, "SemTyID", "");
		}
		
	} else {
		string condition = condition_pre;
		string sem = sem_pre;
		database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
		add_variable_to_table(sem, "SemTyID", "");
	}

	multiedge = solver->get_map_idx_val(operators->name(name)).size();

	prev_bb = bb;
	assigns_map.clear();
	last_operation.clear();
	lockunlock_pre = "unlock";
	condition_pre = "";

	if(multiedge){
		last_idx_val = solver->get_map_idx_val(operators->name(name));
	} else {
		sem_pre = sem_name(solver->get_name_hint("mem_" + solver->realvalue(operators->name(name))));
	}

}

string invert_polarity(string polarity){
	if(polarity == "=") return "#";
	if(polarity == "#") return "=";
	if(polarity == "<") return ">=";
	if(polarity == ">") return "<=";
	if(polarity == ">=") return "<";
	if(polarity == "<=") return ">";

	assert(0 && "Unknown polarity");
}

string Uppaal::invert_condition(string cond){
	string polarity = tokenize(cond, " ")[1];
	myReplace(cond, polarity, invert_polarity(polarity));
	return cond;
}

void c_condition(string& condition_pre){
	myReplace(condition_pre, " # ", " != ");
	myReplace(condition_pre, " = ", " == ");
	myReplace(condition_pre, "constant_IntegerTyID32_", "");
}

void Uppaal::br_instr_cond(string cmp, bool invert){

	printf("\e[31m uppaal::br_instr_cond \e[0m %s\n",cmp.c_str());

	static int n;
	if(n++ > options->cmd_option_int("max_depth")){
		database->insert_uppaal_variables(variables);
		exit(0);
	}

	if(options->cmd_option_bool("no_uppaal_if")){
		if(invert) comparison = invert_condition(comparison);
		condition_pre += " && " + comparison;
		c_condition(condition_pre);
	} else {
		string bb = call_stack() + uppaal_function(operators->get_actual_function()) + "_cond_" + operators->get_actual_bb(); if(bb.substr(0,1) == "_") bb = bb.substr(1);
		string condition = condition_pre;
		string sem = sem_pre;
		string lockunlock = lockunlock_pre;
		string assigns = concat(assigns_map);

		database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
		add_variable_to_table(sem, "SemTyID", "");

		multiedge = 0;

		condition_pre = comparison;
		if(invert) condition_pre = invert_condition(condition_pre);
		c_condition(condition_pre);
		prev_bb = bb;
		assigns_map.clear();
		last_operation.clear();
		sem_pre = "";
		lockunlock_pre = "";
	}

}

void Uppaal::end_sim(){

	printf("\e[31m uppaal::end_sim\e[0m\n");


	string bb = options->cmd_option_str("seedfn") + "_" + "end"; if(bb.substr(0,1) == "_") bb = bb.substr(1);
	string lockunlock = lockunlock_pre;
	string assigns = concat(assigns_map);
	if(multiedge){
		for( map<set<pair<string, int> >, int>::iterator it = last_idx_val.begin(); it != last_idx_val.end(); it++ ){
			set<pair<string, int> > idx_comb = it->first;
			int value = it->second;
			string condition = uppaal_index_condition(idx_comb);
			string sem = sem_name(solver->get_name_hint("mem_" + itos(value)));
			database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
			add_variable_to_table(sem, "SemTyID", "");
		}
		
	} else {
		string condition = condition_pre;
		string sem = sem_pre;
		database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
		add_variable_to_table(sem, "SemTyID", "");
	}




	database->insert_uppaal_variables(variables);

}

string Uppaal::content(string name){

	if(name.substr(0,9) == "constant_") return tokenize(name, "_")[2];
	if( assigns_map[name] == "" ) return uppaal_name(name);
	else return assigns_map[name];
}

bool Uppaal::is_cmp(string operation){


	if( operation == "<="  ) return true;
	if( operation == "<"   ) return true;
	if( operation == "="   ) return true;
	if( operation == ">="  ) return true;
	if( operation == ">"   ) return true;
	if( operation == "#"   ) return true;
	if( operation == "u<=" ) return true;
	if( operation == "u<"  ) return true;
	if( operation == "u>=" ) return true;
	if( operation == "u>"  ) return true;

	return false;

}

int order(string operation){
	if(operation == "+") return 3;
	if(operation == "-") return 3;
	if(operation == "*") return 2;
	if(operation == "%") return 2;
	if(operation == "<=") return 1;
	if(operation == "<") return 1;

	printf("operation %s\n", operation.c_str());
	assert(0 && "Unknown operator");
}

int min(int a, int b){
	return a<b?a:b;
}

void Uppaal::binary_instruction(string dst, string op1, string op2, string operation){

	printf("uppaal::binary_instruction %s %s %s %s\n", dst.c_str(), op1.c_str(), op2.c_str(), operation.c_str());

	if(is_cmp(operation)){
		//comparison = dst;
		comparison = op1 + " " + operation + " " + op2;
	}

	string content1;
	string content2;

	if(last_operation[op1] == "" || order(operation) >= order(last_operation[op1]))
		content1 = content(op1);
	else
		content1 = "(" + content(op1) + ")";

	if(last_operation[op2] == "" || order(operation) >= order(last_operation[op2]))
		content2 = content(op2);
	else
		content2 = "(" + content(op2) + ")";

	assigns_map[dst] = content1 + " " + operation + " " + content(op2);

	last_operation[dst] = operation;

	add_variable_to_table(dst, solver->get_type(dst), "");
	add_variable_to_table(op1, solver->get_type(dst), "");
	add_variable_to_table(op2, solver->get_type(dst), "");
}

void Uppaal::assign_instruction(string src, string dst, string fn_name ){

	printf("uppaal::assign_instruction %s %s %s\n", src.c_str(), dst.c_str(), fn_name.c_str());

	assigns_map[dst] = content(src);

	last_operation[dst] = last_operation[src];

	add_variable_to_table(dst, solver->get_type(dst), "");
	add_variable_to_table(src, solver->get_type(src), "");

}

void Uppaal::assign_global(string src, string dst){

	static string globalname;

	printf("uppaal::assign_global %s %s\n", src.c_str(), solver->get_name_hint(dst).c_str());

	if(dst.substr(0,7) == "global_"){
		globalname = dst;
	}
	
	
	if(dst.substr(0,4) == "mem_"){
		add_variable_to_table(globalname, solver->get_type(src), src );
	}
	
	
}

void Uppaal::add_variable_to_table(string name, string type, string init){

	if(name == "") return;

	printf("uppaal::add_variable_to_table %s %s %s\n", name.c_str(), type.c_str(), init.c_str() );
	UppaalVar uppaal_var_1 = {name, type, init};
	UppaalVar uppaal_var_2 = {uppaal_name(name), type, init};

	//variables.insert(uppaal_var_1);
	variables.insert(uppaal_var_2);
}


void Uppaal::add_eq_set(set<pair <string, int> > idx_val){
	

	printf("\e[31m uppaal::add_eq_set \e[0m %s\n", and_cond(idx_val).c_str());


	string bb = call_stack() + operators->get_actual_function() + "_array_" + operators->get_actual_bb(); if(bb.substr(0,1) == "_") bb = bb.substr(1);
	bb_counter[bb]++;
	bb += "_" + itos(bb_counter[bb]);
	string condition = condition_pre;
	string sem = sem_pre;
	string lockunlock = lockunlock_pre;
	string assigns = concat(assigns_map);

	database->insert_uppaal_row(prev_bb, bb, condition, sem, lockunlock, assigns);
	add_variable_to_table(sem, "SemTyID", "");

	condition_pre = and_cond(idx_val);
	c_condition(condition_pre);
	prev_bb = bb;
	assigns_map.clear();
	last_operation.clear();
	sem_pre = "";
	lockunlock_pre = "";


}





string Uppaal::and_cond( set<pair<string,int> > idx_val){

	string ret;

	for( set<pair<string, int> >::iterator it = idx_val.begin(); it != idx_val.end(); it++ ){
		ret += " && " + it->first + " = " + itos(it->second);
	}
	
	ret = ret.substr(4);

	return ret;

}



string Uppaal::call_stack(){
	string ret;
	for( vector<string>::iterator it = function_stack.begin(); it != function_stack.end(); it++ ){
		ret += (*it);
	}
	
	myReplace(ret, "_", "");
	ret += call_id_m;

	long crc = rc_crc32(0, ret.c_str(), ret.length());

	ret = "a" + itos(abs(crc));

	return ret;
}

void Uppaal::BeginFn(char* _fn_name){
	string fn_name = string(_fn_name);
	function_stack.push_back(fn_name);
}

void Uppaal::EndFn(){
	function_stack.erase(function_stack.end()-1);
}

void Uppaal::call_id(char* _call_id){
	//printf("uppaal::call_id %s\n", _call_id);
	call_id_m = string(_call_id);
}

