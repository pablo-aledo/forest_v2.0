/*
 * =====================================================================================
 * /
 * |     Filename:  all_solvers.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/07/2014 04:24:00 PM
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

#include "all_solvers.h"
#include "options.h"

extern Options* options;

AllSolvers::AllSolvers(){

	string selected_driver = options->cmd_option_str("driver");

	Z3BitVector*       solver_bitvector    = new Z3BitVector;
	LinearSolver*      solver_linear       = new LinearSolver;
	PolynomicSolver*   solver_polynomic    = new PolynomicSolver;
	Z3RealInt*         solver_realint      = new Z3RealInt;
	MixedInt*          solver_mixedint     = new MixedInt;
	MixedBblast*       solver_mixedbblast  = new MixedBblast;
	LinearBblast*      solver_linearbblast = new LinearBblast;


	if(selected_driver != "bitvector")     solvers.push_back( solver_bitvector    );
	if(selected_driver != "linear")        solvers.push_back( solver_linear       );
	if(selected_driver != "polynomic")     solvers.push_back( solver_polynomic    );
	if(selected_driver != "mixed_int")     solvers.push_back( solver_mixedint     );
	if(selected_driver != "mixed_bblast")  solvers.push_back( solver_mixedbblast  );
	if(selected_driver != "linear_bblast") solvers.push_back( solver_linearbblast );
	if(selected_driver != "real_integer")  solvers.push_back( solver_realint      );

	if(selected_driver == "bitvector")    { solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "linear")       { solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "polynomic")    { solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "mixed_int")    { solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "mixed_bblast") { solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "linear_bblast"){ solver_realint->set_isdriver(); driver = solver_realint; }
	if(selected_driver == "real_integer") { solver_realint->set_isdriver(); driver = solver_realint; }
}

AllSolvers::~AllSolvers(){
	
}

void AllSolvers::assign_instruction_content(string src, string dst, string fn_name){

	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->assign_instruction_content(src,dst, fn_name);
	}
	driver->get_context(this);
	driver->assign_instruction_content(src,dst, fn_name);
	get_context_back(driver);
}

string AllSolvers::internal_condition(string condition){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->internal_condition(condition);
	}
	driver->get_context(this);
	string ret = driver->internal_condition(condition);
	get_context_back(driver);
	return ret;
}

void AllSolvers::binary_instruction_content(string dst, string op1, string op2, string operation){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->binary_instruction_content(dst, op1, op2, operation);
	}
	driver->get_context(this);
	driver->binary_instruction_content(dst, op1, op2, operation);
	get_context_back(driver);
}

void AllSolvers::solve_problem(){
	printf("allsolvers_solve_problem\n"); fflush(stdout);
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		printf("solve with particular solver\n"); fflush(stdout);
		(*it)->get_context(this);
		(*it)->solve_problem();
	}
	printf("solve with driver\n");
	driver->get_context(this);
	driver->solve_problem();
	get_context_back(driver);
}

string AllSolvers::internal_representation(int in, string type){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->internal_representation(in, type);
	}
	driver->get_context(this);
	string ret = driver->internal_representation(in, type);
	get_context_back(driver);
	return ret;
}

void AllSolvers::cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->cast_instruction(src, dst, type_src, type_dst, sext);
	}
	driver->get_context(this);
	driver->cast_instruction(src, dst, type_src, type_dst, sext);
	get_context_back(driver);
}

map<set<pair<string, int> > , int > AllSolvers::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->get_idx_val(base,idx_content,  indexes, first_address, last_address);
	}
	driver->get_context(this);
	map<set<pair<string, int> > , int > ret = driver->get_idx_val(base,idx_content,  indexes, first_address, last_address);
	get_context_back(driver);
	return ret;
}

void AllSolvers::clear_variable(string var){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->clear_variable(var);
	}
	driver->get_context(this);
	driver->clear_variable(var);
	get_context_back(driver);
}

void AllSolvers::save_first_content(string var, string dst){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->save_first_content(var, dst);
	}
	driver->get_context(this);
	driver->save_first_content(var, dst);
	get_context_back(driver);
}

void AllSolvers::sym_store(string src, string addr){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->sym_store(src, addr);
	}
	driver->get_context(this);
	driver->sym_store(src, addr);
	get_context_back(driver);
}

void AllSolvers::sym_load(string dst, string idx_content){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->sym_load(dst, idx_content);
	}
	driver->get_context(this);
	driver->sym_load(dst, idx_content);
	get_context_back(driver);
}

void AllSolvers::push_condition_static_var(string cond, bool invert){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->push_condition_static_var(cond, invert);
	}
	driver->get_context(this);
	driver->push_condition_static_var(cond, invert);
	get_context_back(driver);
}

void AllSolvers::load_state(){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->load_state();
	}
	driver->get_context(this);
	driver->load_state();
	get_context_back(driver);
}

void AllSolvers::save_state(){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->save_state();
	}
	driver->get_context(this);
	driver->save_state();
	get_context_back(driver);
}

void AllSolvers::variable_store(string src,string idx_content, int first_address, int last_address ){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->variable_store(src,idx_content, first_address, last_address );
	}
	driver->get_context(this);
	driver->variable_store(src,idx_content, first_address, last_address );
	get_context_back(driver);
}

void AllSolvers::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->pointer_instruction(dst, offset_tree,  indexes, base);
	}
	driver->get_context(this);
	driver->pointer_instruction(dst, offset_tree,  indexes, base);
	get_context_back(driver);
}

string AllSolvers::debug_content( string name ){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->debug_content( name );
	}
	driver->get_context(this);
	string ret = driver->debug_content( name );
	get_context_back(driver);
	return ret;
}

void AllSolvers::set_sat(bool _sat){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->set_sat(_sat);
	}
	driver->get_context(this);
	driver->set_sat(_sat);
	get_context_back(driver);
}

int AllSolvers::show_problem(){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->show_problem();
	}
	driver->get_context(this);
	int ret = driver->show_problem();
	get_context_back(driver);
	return ret;
}

bool AllSolvers::solvable_problem(){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->solvable_problem();
	}
	driver->get_context(this);
	bool ret = driver->solvable_problem();
	get_context_back(driver);
	return ret;
}

void AllSolvers::set_offset_tree( string varname, string tree ){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->set_offset_tree( varname, tree );
	}
	driver->get_context(this);
	driver->set_offset_tree( varname, tree );
	get_context_back(driver);
}

string AllSolvers::canonical_representation(string in){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->canonical_representation(in);
	}
	driver->get_context(this);
	string ret = driver->canonical_representation(in);
	get_context_back(driver);
	return ret;
}

void AllSolvers::bool_to_int8(string src, string dst){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->bool_to_int8(src, dst);
	}
	driver->get_context(this);
	driver->bool_to_int8(src, dst);
	get_context_back(driver);
}

void AllSolvers::bool_to_int32(string src, string dst){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->bool_to_int32(src, dst);
	}
	driver->get_context(this);
	driver->bool_to_int32(src, dst);
	get_context_back(driver);
}



string AllSolvers::content_smt(string name){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->content_smt(name);
	}
	driver->get_context(this);
	string ret = driver->content_smt(name);
	get_context_back(driver);
	return ret;
}

void AllSolvers::push_condition_var(string name, bool invert ){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->push_condition_var(name, invert );
	}
	driver->get_context(this);
	driver->push_condition_var(name, invert );
	get_context_back(driver);
}

void AllSolvers::propagate_unary_extra(string src, string dst, bool forcedfree){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->propagate_unary_extra(src, dst, forcedfree);
	}
	driver->get_context(this);
	driver->propagate_unary_extra(src, dst, forcedfree);
	get_context_back(driver);
}

void AllSolvers::propagate_binary_extra(string op1, string op2, string dst){
	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->get_context(this);
		(*it)->propagate_binary_extra(op1, op2, dst);
	}
	driver->get_context(this);
	driver->propagate_binary_extra(op1, op2, dst);
	get_context_back(driver);

}



void AllSolvers::add_eq_zero(string variable){

	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->add_eq_zero(variable);
	}
	driver->add_eq_zero(variable);

}


void AllSolvers::add_neq_zero(string variable){


	for( vector<SolverWrapper*>::iterator it = solvers.begin(); it != solvers.end(); it++ ){
		(*it)->add_neq_zero(variable);
	}
	driver->add_neq_zero(variable);

}


void AllSolvers::dump_conditions(stringstream& sstream){
	assert(0 && "Not Implemented");
}




void AllSolvers::dump_model(){

	assert(0 && "Not implemented");

}



map<set<pair <string, int> >, int> AllSolvers::get_map_idx_val(string name){
	assert(0 && "Not Implemented");
}


void AllSolvers::add_eq_set(set<pair <string, int> > set_idx_val){
	assert(0 && "Not Implemented");
}




void AllSolvers::set_content(string name, string value){

	assert(0 && "not implemented");

}

string AllSolvers::eval(string expression){
	assert(0 && "Not Implemented");
}

void AllSolvers::add_bt(string var, string val){

	assert(0 && "Not Implemented");

}

void AllSolvers::add_lt(string var, string val){

	assert(0 && "Not Implemented");

}


pair<int, int> AllSolvers::get_range(string name){

	assert(0 && "Not Implemented");

}


bool AllSolvers::empty_assertions(){

	assert(0 && "Not Implemented");

}






void AllSolvers::add_smt(string smt){

	assert(0 && "Not Implemented");

}
