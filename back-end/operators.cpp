/*
 * =====================================================================================
 * /
 * |     Filename:  operators.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:48 PM
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

#include "operators.h"
#include <sys/wait.h>
#include "database.h"
#include "utils.h"
#include "options.h"
#include "timer.h"
#include "z3_solver.h"
#include "uppaal.h"
#include "architecture.h"
#include "concurrency_backend.h"
#include "pre_post.h"

#define UNDERSCORE "_"

#define debug true

extern Options* options;
extern Operators* operators;
extern SolverWrapper* solver;
extern Database* database;
extern Timer* timer;
extern Uppaal* uppaal;
extern map<string, string> map_pos_to_last_store;
extern Concurrency* concurrency;
extern PrePost* pre_post;

Operators::Operators(){

	alloca_pointer = 0;

}

Operators::~Operators(){}

void Operators::cast_instruction(char* _dst, char* _src, char* _type, char* _sext){

	string dst = string(_dst);
	string src = string(_src);
	string dst_type = string(_type);
	string src_type = solver->gettype(name(src)).c_str();
	string sext = string(_sext);

	if(src.substr(0,9) == "function_"){
		printf("src %s\n", src.c_str());
		src = src.substr(9);
		myReplace(src, "_", "underscore");
		src = "constant_FunctionTyID_function" + src;
		printf("src %s\n", src.c_str());
	}

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for cast_instruction");
	if(!check_mangled_name(name(src))) assert(0 && "Wrong src for cast_instruction");

	solver->cast_instruction(name(src),name(dst), src_type, dst_type, sext);


	if( solver->get_type(name(src)) != "bool" )
		solver->settype(name(dst), dst_type);
	else
		solver->settype(name(dst), "bool");

	if(solver->get_type(name(src)) == "bool" && dst_type == "IntegerTyID8"){

		solver->bool_to_int8(name(src), name(dst));
		//solver->settype(name(dst), "IntegerTyID8");
		solver->settype(name(dst), dst_type);

		if(solver->realvalue(name(src)) == "true")
			solver->set_real_value(name(dst), "1");
		else if(solver->realvalue(name(src)) == "false")
			solver->set_real_value(name(dst), "0");
		else{
			if(options->cmd_option_bool("sequentialize"))
				solver->set_real_value(name(dst), "0");
			else
				assert(0 && "real_value of bool should be true or false");
		}

		//printf("casting bool to integertyid8 %s\n", solver->content(name(dst)).c_str());

	}


	if(solver->get_type(name(src)) == "bool" && dst_type == "IntegerTyID32"){

		solver->bool_to_int32(name(src), name(dst));
		//solver->settype(name(dst), "IntegerTyID8");
		solver->settype(name(dst), dst_type);

		if(solver->realvalue(name(src)) == "true")
			solver->set_real_value(name(dst), "1");
		else if(solver->realvalue(name(src)) == "false")
			solver->set_real_value(name(dst), "0");
		else
			assert(0 && "real_value of bool should be true or false");

		//printf("casting bool to integertyid8 %s\n", solver->content(name(dst)).c_str());

	}



	debug && printf("\e[31m Cast_instruction %s %s %s %s %s\e[0m. %s %s %s %s\n", name(dst).c_str(), name(src).c_str(),
									src_type.c_str(), dst_type.c_str(), solver->gettype(name(dst)).c_str(),
		                                                              name(src).c_str(), realvalue(src).c_str(),
		                                                              name(dst).c_str(), realvalue(dst).c_str()  );


}

void Operators::pr_callstack(){
	for( vector<pair<string, string> >::iterator it = callstack.begin(); it != callstack.end(); it++ ){
		printf("\e[36m callstack %s %s\e[0m \n", it->first.c_str(), it->second.c_str() );
	}
}

void Operators::BeginFn(char* _fn_name, char* _fn_oplist ){

	string fn_name = string(_fn_name);
	vector<string> fn_oplist = tokenize(_fn_oplist, ",");

	debug && printf("\e[36m begin_fn %s \e[0m\n", _fn_name);


	myReplace(fn_name, UNDERSCORE, "");




	for ( unsigned int i = 0; i < oplist_gl.size(); i++) {

		printf("\e[34m actual %s formal %s\e[0m \n", name(oplist_gl[i]).c_str(), name(fn_oplist[i], fn_name).c_str() );

		solver->assign_instruction(
				name(oplist_gl[i]),
				name(fn_oplist[i], fn_name)
				);

		set_name_hint(name(fn_oplist[i], fn_name), "argument_" + itos(i) + "_" + fn_name );



	}

	actual_function = fn_name;
	myReplace(actual_function, UNDERSCORE, "underscore");

	callstack.push_back( pair<string, string>(ret_to_gl, actual_function) );

	pr_callstack();

	if(pre_post->get_preconditions(fn_name).size() && options->cmd_option_bool("check_preconditions")){
		pre_post->check_preconditions( pre_post->get_preconditions(fn_name) );
	}



}

string Operators::flat_function_stack(){

	string ret;

	for( vector<pair<string, string> >::iterator it = callstack.begin(); it != callstack.end(); it++ ){
		ret += it->second;
	}
	

	return ret;
}

void Operators::CallInstr_post( char* _fn_name, char* _ret_type, char* _caller ){

	if(string(_fn_name) == "malloc") _fn_name = "fr_malloc";
	if(string(_fn_name) == "free") _fn_name = "fr_free";
	if(string(_fn_name) == "alloca") _fn_name = "fr_alloca";

	int prev_callstack_size = callstack_size;
	int callstack_size_local = callstack.size();

	//printf("prev_callstack_size %d callstack_size_local %d\n", prev_callstack_size, callstack_size_local);
	
	//printf("prev_name %s name %s\n", callstack[callstack.size()-1].second.c_str(), _fn_name);
	//bool annotated = (prev_callstack_size != callstack_size_local);
	
	string n1 = callstack[callstack.size()-1].second;
	string n2 = string(_fn_name);


	if(n2.substr(0, 9) == "register_"){
		string caller = string(_caller);
		myReplace(caller, "_", "");
		string var = name(n2, caller);
		string pointedfn = solver->realvalue_mangled(name(n2,caller));
		printf("\e[36m Function_pointer \e[0m caller %s var %s pointed %s n2 %s\n", caller.c_str(), var.c_str(), pointedfn.c_str(), n2.c_str() );
		n2 = solver->realvalue_mangled(var);
		//printf("1 now n2 is %s\n", n2.c_str());
		if(n2.substr(0,22) == "constant_FunctionTyID_"){
			myReplace(n2, "constant_FunctionTyID_", "");
			//printf("4 now n2 is %s\n", n2.c_str());
		} else {
			n2 = realvalue("mem_" + n2);
			//printf("2 now n2 is %s\n", n2.c_str());
			myReplace(n2, "constant_FunctionTyID_", "");
			//printf("3 now n2 is %s\n", n2.c_str());
		}
		assert(n2.substr(0,8) == "function" && "This is not a function");
		n2 = n2.substr(8);
	}



	myReplace(n1, UNDERSCORE, "");
	myReplace(n2, UNDERSCORE, "");
	myReplace(n2,"underscore", "");

	assert(n1 != "" && "Empty function_name");
	assert(n2 != "" && "Empty function_name");
	

	printf("\e[36m check_annotated with \e[0m %s %s\n", n1.c_str(), n2.c_str());

	bool annotated = ( n1 == n2 );


	//if(n2 == "frmalloc") annotated = false;
	//if(n2 == "frfree") annotated = false;

	debug && printf("\e[31m CallInstr_post %s %s \e[0m. ret_to_gl %s annotated %d(%s %s) \n", _fn_name, _ret_type, ret_to_gl.c_str(), annotated, n1.c_str(), n2.c_str() );

	pr_callstack();

	string fn_name = string(_fn_name);
	myReplace(fn_name, "_", "");
	if(pre_post->get_postconditions(fn_name).size() && options->cmd_option_bool("use_postconditions")){
		pre_post->add_postconditions( pre_post->get_postconditions(fn_name) );
	}

	if(!annotated){
		NonAnnotatedCallInstr( _fn_name, _ret_type );
		return;
	}


	if( callstack.size() == 0 ){

		debug && printf("\e[36m Empty Call-Stack\e[0m.\n" );
		return;
	};
	if( ret_gl == "register_" ){

		callstack.erase( callstack.end() - 1 );
		string last_fn_callstack = callstack[ callstack.size() - 1].second;

		actual_function = last_fn_callstack;

		return;
	}

	string last_rg_callstack = callstack[ callstack.size() - 1].first;
	string last_fn_callstack = callstack[ callstack.size() - 1].second;
	callstack.erase( callstack.end() - 1 );
	actual_function = callstack[ callstack.size() - 1].second;

	solver->assign_instruction( name(ret_gl, last_fn_callstack), name(last_rg_callstack), actual_function ); // src, dst, fnname

	debug && printf("\e[36m Continuing function %s \e[0m.\n", actual_function.c_str() );

}

void Operators::NonAnnotatedCallInstr( char* _fn_name, char* _ret_type ){


	debug && printf("\e[33m NonAnnotatedCallInstr %s %s %s\e[0m\n", _fn_name, _ret_type, ret_to_gl.c_str() );
	string fn_name           = string(_fn_name);
	string ret_to            = ret_to_gl;
	string ret_type          = string(_ret_type);

	//printf("nonannotatedcallinstr %s\n", name(ret_to).c_str());
	//solver->initialize_var(name(ret_to));

	if(nonannotated_call_count[fn_name] == 0){
		//solver->initialize_var(name(ret_to));
		set_name_hint(name(ret_to), "return_of_" + fn_name );
	} else {
		set_name_hint(name(ret_to), "return_of_" + fn_name + "_" + itos(nonannotated_call_count[fn_name]) );
		//solver->insert_variable(name(ret_to), "return_of_" + fn_name );
		for ( unsigned int i = 0; i < nonannotated_call_count[fn_name]; i++) {
			if( i == 0 )
				solver->insert_variable(name(ret_to), "return_of_" + fn_name );
			else
				solver->insert_variable(name(ret_to), "return_of_" + fn_name + "_" + itos(i) );
		}
	}

	nonannotated_call_count[fn_name]++;


	solver->settype(name(ret_to), ret_type );
	solver->set_comes_from_non_annotated(name(ret_to));
	//solver->set_real_value(name(ret_to), "0");
	solver->initialize_real_value(name(ret_to), solver->get_name_hint(name(ret_to)));

	debug && printf("\e[31m NonAnnotatedCallInstr %s %s\e[0m\n", _fn_name, _ret_type );
}

void Operators::CallInstr( char* _oplist, char* _ret_to ){


	vector<string> oplist    = tokenize( string(_oplist), ",");
	string ret_to = string(_ret_to);
	callstack_size = callstack.size();

	debug && printf("\e[31m CallInstr %s %s\e[0m. \e[36m cs_size %d\e[0m \n", _oplist, _ret_to, callstack_size );

	pr_callstack();

	oplist_gl.clear();
	for ( unsigned int i = 0; i < oplist.size(); i++) {

		if( oplist[i].substr(0,9) == "function_" ){
			string to_insert = oplist[i];
			myReplace(to_insert, "_", "");
			myReplace(to_insert, "function", "constant_FunctionTyID_function");
			debug && printf("\e[31m Saving %s\e[0m\n", to_insert.c_str() );
			oplist_gl.push_back(to_insert);
		} else {
			debug && printf("\e[31m Saving %s\e[0m\n", oplist[i].c_str() );
			oplist_gl.push_back(oplist[i]);
		}



	}


	ret_to_gl = ret_to;

}

void Operators::ReturnInstr(char* _retname ){

	string retname = string(_retname);

	if(!check_mangled_name(name(retname))) assert(0 && "Wrong return name for ReturnInstr");

	ret_gl = retname;



	debug && printf("\e[31m ReturnInstr %s \e[0m size %lu \n", _retname, callstack.size() );


}

void Operators::select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){

	string dest = string(_dest);
	string cond = string(_cond);
	string sel1 = string(_sel1);
	string sel2 = string(_sel2);

	if( realvalue(cond) == "true" ){

		solver->assign_instruction( name(sel1), name(dest)  );

	} else if( realvalue(cond) == "false" ){

		solver->assign_instruction( name(sel2), name(dest)  );

	} else {
		assert(0 && "Not binary condition");
	}

	debug && printf("\e[31m select_op %s %s %s %s\e[0m\n", _dest, _cond, _sel1, _sel2);

}

void Operators::binary_op(char* _dst, char* _op1, char* _op2, char* _operation){

	string dst = string(_dst);
	string op1 = string(_op1);
	string op2 = string(_op2);
	string operation = string(_operation);


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for binary_op");
	if(!check_mangled_name(name(op1))) assert(0 && "Wrong op1 for binary_op");
	if(!check_mangled_name(name(op2))) assert(0 && "Wrong op2 for binary_op");


	solver->binary_instruction(name(dst),name(op1),name(op2),operation);


	//solver->set_real_value(name(dst), trunc(solver->realvalue(name(dst)), solver->gettype(name(dst))) );


	debug && printf("\e[31m binary_operation %s %s %s %s\e[0m. %s %s %s %s %s %s\n", _dst, _op1, _op2, _operation, 
			                                                        op1.c_str(), realvalue(op1).c_str(),
									        op2.c_str(), realvalue(op2).c_str(),
										_dst, realvalue(dst).c_str() );

}


void Operators::load_instr(char* _dst, char* _addr){

	string dst = string(_dst);
	string addr = string(_addr);
	string src = "mem" UNDERSCORE + realvalue(addr);

	//solver->initialize_var(name(dst));

	if(solver->get_outofbounds(name(addr))){
		if(!solver->get_free_variables().size() || solver->empty_assertions() ){
			database->insert_outofbounds();
			database->insert_trace();
			printf("Out of Bounds\n");
			exit(0);
		}
		solver->solve_problem();
		if(!solver->solvable_problem())
			exit(0);
		printf("%s\n", name(addr).c_str());
		database->insert_outofbounds();
		database->insert_trace();
		printf("Out of Bounds\n");
		exit(0);
		//assert(0 && "Out of Bounds");
	}

	if(solver->get_is_propagated_constant(name(addr)) || solver->is_constant(name(addr))){
		if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for load");
		if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for load");

		solver->assign_instruction(name(src),name(dst));
	} else {


		solver->sym_load(name(dst), name(addr));

	}

	debug && printf("\e[31m load instruction %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(addr).c_str(),
			name(addr).c_str(), realvalue(addr).c_str(),
			name(src).c_str(), realvalue(src).c_str(),
			name(dst).c_str(), realvalue(dst).c_str()
		       );


	//exit(0);

}


void Operators::fork_on_array(string dst){

	map<set<pair <string, int> >, int> map_idx_val = solver->get_map_idx_val(name(dst));

	printf("fork_on_array %s %lu %s\n", dst.c_str(), map_idx_val.size(), solver->content_smt(name(dst)).c_str()); fflush(stdout);
	int count = 0;

	for( map<set<pair <string, int> >, int>::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair <string, int> > idx_val = it->first;
		int value = it->second;

		for( set<pair<string,int> >::iterator it2 = idx_val.begin(); it2 != idx_val.end(); it2++ ){
			printf("fork_on_array_idx_val %s %d %d\n", it2->first.c_str(), it2->second, value);
		}
		

		if(pid_t pid = fork()){
			int status;
			waitpid(pid, &status, 0);
			count++;
		} else {

			solver->add_eq_set(idx_val);
			
			if(options->cmd_option_bool("generate_uppaal_model"))
				uppaal->add_eq_set(idx_val);
			solver->assign_instruction(  "constant_PointerTyID_" + itos(value)   , name(dst));
			solver->solve_problem();
			if(!solver->solvable_problem()) exit(0);
			break;

		}

	}

	if(count == map_idx_val.size())
		exit(0);


}




void Operators::store_instr(char* _src, char* _addr){

	//debug && printf("\e[33m store instruction\e[0m\n"); fflush(stdout);
	//debug && printf("\e[33m store instruction %s %s\e[0m\n", _src, _addr ); fflush(stdout);


	string src = string(_src);
	string addr = string(_addr);
	string dst = "mem" UNDERSCORE + realvalue(string(_addr)) ;

	if(src.substr(0,9) == "function_"){
		string fn_name = src;
		myReplace(fn_name, "function_", "function");
		string constant_name = "constant_FunctionTyID_" + fn_name;
		//printf("fn_name %s constant_name %s\n", fn_name.c_str(), constant_name.c_str());
		//alloca_instr( (char*)constant_name.c_str(), "FunctionTyID");
		alloca_instr( "register_forestfp", "FunctionTyID");
		printf("FINALLOCA\n");
		solver->assign_instruction( constant_name, "mem_" + realvalue("register_forestfp"));
		printf("FINASSIGN1\n");
		solver->assign_instruction( "constant_PointerTyID_" + realvalue("register_forestfp") , name(dst));
		printf("FINASSIGN2\n");
		return;
	}


	if(solver->get_outofbounds(name(addr))){
		printf("%s\n", name(addr).c_str());
		database->insert_outofbounds();
		printf("Out_of_bounds\n");
		exit(0);
	}


	if(solver->get_is_propagated_constant(name(addr)) || solver->is_constant(name(addr))){


		if(!check_mangled_name(name(src))) assert(0 && "Wrong src for store");
		if(!check_mangled_name(name(addr))) assert(0 && "Wrong addr for store");
		if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for store");

		solver->assign_instruction(name(src),name(dst));

	} else {

		solver->sym_store(name(src), name(addr));

	}

	debug && printf("\e[31m store instruction %s %s\e[0m %s %s %s %s %s %s\n",name(src).c_str(), name(addr).c_str(),
			name(src).c_str(), realvalue(src).c_str(),
			name(addr).c_str(), realvalue(addr).c_str(),
			name(dst).c_str(), realvalue(dst).c_str() );

}


void Operators::cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){

	string dst  = string(_dst);
	string cmp1 = string(_cmp1);
	string cmp2 = string(_cmp2);
	string type = string(_type);

	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for compare");
	if(!check_mangled_name(name(cmp1))) assert(0 && "Wrong cmp1 for compare");
	if(!check_mangled_name(name(cmp2))) assert(0 && "Wrong cmp2 for compare");


	solver->binary_instruction(name(dst),name(cmp1),name(cmp2), type);

	debug && printf("\e[31m cmp_instr %s %s %s %s\e[0m. %s %s %s %s %s %s\n", name(dst).c_str(), name(cmp1).c_str(), name(cmp2).c_str(), type.c_str(), 
			                                                 name(cmp1).c_str(), realvalue(cmp1).c_str(),
									 name(cmp2).c_str(), realvalue(cmp2).c_str(),
									 name(dst).c_str(), realvalue(dst).c_str() );

	solver->settype(name(dst), "bool");

	assert( (realvalue(dst) == "true" || realvalue(dst) == "false") && "Invalid result for a comparison operation" );
}

void Operators::br_instr_incond(){

	debug && printf("\e[31m inconditional_branch_instr\e[0m\n" );


	if(options->cmd_option_str("solver") == "interpolants")
		solver->push_condition_var("", false);

}

void Operators::push_function_and_bb(string function_and_bb){
	functions_and_bbs.push_back(function_and_bb);
}

vector<string> Operators::get_functions_and_bbs_trace(){
	return functions_and_bbs;
}

void Operators::begin_bb(char* name){

	//solver->show_assigns();

	actual_bb = string(name);

	if( options->cmd_option_bool("follow_path") || options->cmd_option_bool("single_step") )
		database->insert_last_bb(actual_function, actual_bb);

	string function_and_bb = actual_function + "_" + actual_bb;


	push_function_and_bb(function_and_bb);

	if(actual_bb == "ERROR"){
		if(solver->has_free_variables())
			solver->solve_problem();
		database->insert_problem();
		database->insert_trace();
		printf("Node Hitted\n");
		end_sim();
		exit(0);
	}


	if(options->cmd_option_bool("single_step") && function_and_bb == options->cmd_option_str("target_node")){
		//solver->show_problem();
		solver->solve_problem();
		database->insert_problem();
		database->insert_trace();
		printf("Node Hitted\n");
		exit(0);
	}




	debug && printf("\e[36m begin_bb %s (fn %s)\e[0m\n", name, actual_function.c_str() );
}

void Operators::end_bb(char* name){
	if(database->already_covered_at_bb(name)) exit(0);
	debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

void Operators::global_var_init(char* _varname, char* _type, char* _values){

	//printf("\e[33m global_var_init %s %s %s\e[0m.\n", _varname, _type, _values); fflush(stdout);

	string varname        = string(_varname);
	string type           = string(_type);
	vector<string> types = tokenize(string(_type), ",");
	vector<string> values = tokenize(string(_values), ",");

	//solver->initialize_var(name(varname));

	timer->start_timer();
	int last_address = alloca_pointer + get_size(type) - get_size(types[types.size()-1]);
	int first_address = alloca_pointer;
	timer->end_timer("global_boundaries");


	if( types.size() != values.size() ){
		printf("%lu %lu\n", types.size(), values.size() );
		assert( 0 && "Different number of types and values");
	}

	if(!check_mangled_name(name(varname))) assert(0 && "Wrong name for global_var_init");

	solver->set_assigning_globals(1);

	timer->start_timer();
	stringstream rvalue; rvalue << "constant_PointerTyID_" << alloca_pointer;
	solver->assign_instruction(name(rvalue.str()), name(varname));
	solver->settype( name(varname), "Pointer");
	timer->end_timer("global_assign");

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int prev_alloca_pointer = alloca_pointer;

	timer->start_timer();
	for ( unsigned int i = 0; i < values.size(); i++) {

		stringstream mem_var; mem_var << "mem" UNDERSCORE << itos(alloca_pointer);

		solver->settype(mem_var.str(), types[i]);

		if(values[i] != "X"){
			stringstream constant_name; constant_name << values[i];

			solver->assign_instruction( name(constant_name.str()), name(mem_var.str()));
		} else {
			stringstream constant_name; constant_name << "constant_" << types[i] << "_0";

			solver->assign_instruction( name(constant_name.str()), name(mem_var.str()));

		}

		stringstream hint;
		if(values.size() > 1){
			hint << varname << "+" << (alloca_pointer-prev_alloca_pointer);
		} else {
			hint << varname;
		}


		if( solver->is_forced_free_hint(hint.str()) ){
			printf("forced free_hint %s %s\n", hint.str().c_str(), mem_var.str().c_str());
			solver->insert_forced_free_var(mem_var.str());
		}




		set_name_hint(mem_var.str(), hint.str());

		first_addresses[mem_var.str()] = first_address;
		last_addresses[mem_var.str()] = last_address;

		alloca_pointer += get_size(types[i]);
	}

	timer->end_timer("global_values");

	solver->set_assigning_globals(0);

	debug && printf("\e[31m global_var_init %s %s %s\e[0m. %s %s %s %s allocapointer %d last_address %d first_address %d\n", varname.c_str(),type.c_str(),_values 
			, name(varname).c_str(), realvalue(name(varname)).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer
		        , last_address, first_address);
}

void Operators::pointer_ranges(){

	debug && printf("\e[31m pointer_ranges \e[0m\n");

	map<string, Variable> variables = solver->get_map_variables();

	debug && printf("\e[31m variables.size \e[0m %lu\n", variables.size() );


	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		string varname = it->first;
		Variable var = it->second;
		string type = var.type;
		
		debug && printf("\e[31m name \e[0m %s \e[31m type \e[0m %s\n", varname.c_str(), type.c_str() );

		if(type == "PointerTyID" || type == "Pointer" ){
			int first_address = first_addresses["mem_" + solver->realvalue(varname) ];
			int last_address =  last_addresses["mem_" + solver->realvalue(varname) ];

			solver->set_first_address(name(varname), first_address);
			solver->set_last_address(name(varname), last_address);

			debug && printf("\e[31m value \e[0m %s \e[31m first \e[0m %d \e[31m last \e[0m %d \n", solver->realvalue(varname).c_str(), first_address, last_address );
		}
	}


}

void Operators::alloca_instr(char* _reg, char* _subtype){

	string reg = string(_reg);
	string subtypes = string(_subtype);
	vector<string> subtype = tokenize(string(_subtype), ",");

	//printf("\e[33m alloca_instr \e[0m %s %s\n", _reg, _subtype ); fflush(stdout);
	
	//solver->initialize_var(name(reg));

	if(!check_mangled_name(name(reg))) assert(0 && "Wrong name for alloca_instr");


	stringstream rvalue; rvalue << "constant_PointerTyID_" << alloca_pointer;
	solver->settype( name(reg), "Pointer");
	solver->assign_instruction(name(rvalue.str()), name(reg) );

	stringstream mem_var_aux; mem_var_aux << "mem" UNDERSCORE << itos(alloca_pointer);
	int initial_alloca_pointer = alloca_pointer;

	int last_address = alloca_pointer + get_size(subtypes) - get_size(subtype[subtype.size()-1]);
	int first_address = alloca_pointer;

	for ( unsigned int i = 0; i < subtype.size(); i++) {

		stringstream mem_hint;
		stringstream mem_name; mem_name << "mem" UNDERSCORE << itos(alloca_pointer);

		//solver->initialize_var(mem_name.str());
		solver->settype(mem_name.str(), subtype[i]);

		if(subtype.size() == 1)
			mem_hint << actual_function << "_" << reg;
		else 
			mem_hint << actual_function << "_" << reg << "+" << alloca_pointer - initial_alloca_pointer;

		
		//if( forced_free_hints.find(mem_hint.str()) != forced_free_hints.end() ){
		if( solver->is_forced_free_hint(mem_hint.str()) ){
			printf("forced free_hint %s %s\n", mem_hint.str().c_str(), mem_name.str().c_str());
			solver->insert_forced_free_var(mem_name.str());
		}


		set_name_hint(mem_name.str(), mem_hint.str() );
		solver->initialize_real_value(mem_name.str(), mem_hint.str());


		alloca_pointer += get_size(subtype[i]);
	}

	solver->set_last_address(name(reg), last_address);
	solver->set_first_address(name(reg), first_address);


	debug && printf("\e[31m alloca_instr %s %s \e[0m. %s %s %s %s allocapointer %d last_address %d first_address %d\n", name(reg).c_str(), subtypes.c_str(), name(reg).c_str(), realvalue(reg).c_str(), mem_var_aux.str().c_str(), realvalue(mem_var_aux.str()).c_str(), alloca_pointer, solver->get_last_address(name(mem_var_aux.str())), solver->get_first_address(name(mem_var_aux.str())) );
}

int Operators::get_alloca_pointer(){
	return alloca_pointer;
}

void Operators::set_alloca_pointer(int _alloca_pointer){
	printf("operators::set_alloca_pointer %d\n", _alloca_pointer);
	alloca_pointer = _alloca_pointer;
}

bool Operators::all_constant(vector<string> names){

	for( vector<string>::iterator it = names.begin(); it != names.end(); it++ ){
		if(!(solver->is_constant(name(*it)) || solver->get_is_propagated_constant(name(*it)))) return false;
	}

	return true;
	
}

void Operators::getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){

	string dst     = string(_dst);
	string pointer = string(_pointer);
	vector<string> indexes = tokenize(string(_indexes), ",");
	string offset_tree = string(_offset_tree);

	debug && printf("\e[33m getelementptr %s %s %s %s\e[0m.\n", dst.c_str(), pointer.c_str(), _indexes,_offset_tree);

	//solver->initialize_var(name(dst));

	//printf("srctree %s\n", get_offset_tree(pointer).c_str() );


	if(!check_mangled_name(name(dst))) assert(0 && "Wrong dst for getelementptr");
	if(!check_mangled_name(name(pointer))) assert(0 && "Wrong dst for getelementptr");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(name(*it))) assert(0 && "Wrong index for getelementptr");
	}

	//if( get_offset_tree(name(pointer)) != "" && offset_tree == "((0))" ){
		//printf("\e[35m Using source offset_tree \e[0m %s\n", get_offset_tree(name(pointer)).c_str() );
		//offset_tree = get_offset_tree(name(pointer));
	//}
	

	if(all_constant(indexes)){
		solver->set_is_propagated_constant(name(dst));
		string remaining_tree;
		int offset = get_offset(indexes, offset_tree, &remaining_tree);
		solver->set_offset_tree(name(dst), remaining_tree);

		stringstream offset_ss; offset_ss << offset;
		string offset_constant_s = offset_ss.str();
		//offset_constant_s = "constant_" + offset_constant_s;
		offset_constant_s = "constant_PointerTyID_" + itos(offset);

		//printf("offset_constant_s %s\n", offset_constant_s.c_str());

		solver->binary_instruction(name(dst),name(pointer), offset_constant_s, "+");
		//exit(0);
		
		//printf("realvalue_dst %s\n", realvalue(dst).c_str());
		
		//assert( stoi(realvalue(dst)) <= solver->get_last_address(name(pointer)) && "Dereference to value out-of-bounds" );
		if( stoi(realvalue(dst)) > solver->get_last_address(name(pointer)) ) {
			//solver->show_problem();
			debug && printf("\e[33m Access out of bounds dst %d last_address %d\e[0m\n", stoi(realvalue(dst)), solver->get_last_address(name(pointer)));
			solver->set_outofbounds(name(dst));
		}
		if( stoi(realvalue(dst)) < solver->get_first_address(name(pointer)) ){
			//solver->show_problem();
			debug && printf("\e[33m Access out of bounds dst %d first_address %d\e[0m\n", stoi(realvalue(dst)), solver->get_last_address(name(pointer)));
			solver->set_outofbounds(name(dst));
		}


	} else {

		debug && printf("\e[31m non-constant getelementptr \e[0m\n");
		//for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
			//debug && printf("%s %d %d\n", it->c_str(), solver->is_constant(name(*it)), solver->get_is_propagated_constant(name(*it)) );
			////debug && printf("%s\n", it->c_str() );
		//}
		

		solver->pointer_instruction(name(dst), offset_tree, name(indexes), name(pointer) );
		solver->unset_is_propagated_constant(name(dst));

		if(options->cmd_option_bool("fork_on_array")){
			fork_on_array(dst);
			solver->set_is_propagated_constant(name(dst));
		}


		if(options->cmd_option_bool("check_outofbounds")){
			if(int pid = fork()){
				int status; waitpid(pid, &status, 0);
			} else {
				solver->add_bt(name(dst), itos(solver->get_last_address(name(dst))));
				solver->solve_problem();
				if(solver->solvable_problem()){
					solver->set_outofbounds(name(dst));
				}
			}
		}

	




		//string base = pointer;
		//string index_expr = get_index_expr(offset_tree, indexes, base);

		//printf("index_expr %s\n", index_expr.c_str() );

		
	}




	debug && printf("\e[31m getelementptr %s %s %s %s\e[0m. %s realvalue %s, %s realvalue %s lastaddress %d firstaddress %d\n",
			dst.c_str(), pointer.c_str(), _indexes,_offset_tree,
			name(dst).c_str(), realvalue(dst).c_str(), name(pointer).c_str(), realvalue(pointer).c_str(), solver->get_last_address(name(pointer)), solver->get_first_address(name(pointer)) );


}

void Operators::begin_sim(){
	debug && printf("\e[31m Begin Simulation\e[0m\n" );
	database->start_database();

	options->read_options();
	see_each_problem = options->cmd_option_bool("see_each_problem");
	propagate_constants = options->cmd_option_bool("propagate_constants");
	exit_on_insert = options->cmd_option_bool("exit_on_insert");


	solver->load_forced_free_vars();
	solver->load_forced_free_hints();

	if(options->cmd_option_str("file_initializations") != "")
		solver->load_file_initializations();

	//debug = true;//options->cmd_option_bool("debug");

	//alloca_pointer = 0;
}

void Operators::end_sim(){

	if(options->cmd_option_bool("generate_model"))
		solver->dump_model();
	database->save_times();
	database->end_database();

	if(options->cmd_option_bool("get_concurrent_functions"))
		concurrency->end_sim();



	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	
}

string Operators::get_file_initializations(){

	return file_initializations;

}

bool Operators::br_instr_cond(char* _cmp, char* _joints){

	string cmp = string(_cmp);
	vector<string> joints = tokenize(string(_joints), ",");

	if(!check_mangled_name(name(cmp))) assert(0 && "Wrong comparison for break");

	debug && printf("\e[31m conditional_branch_instr %s %s\e[0m. %s %s\n", name(cmp).c_str(),_joints, name(cmp).c_str(), realvalue(cmp).c_str() );

	debug && printf("\e[32m content \e[0m %s \e[32m prop_constant \e[0m %d \e[32m comes_from_non_annotated\e[0m  %d\n", solver->debug_content( name(cmp) ).c_str(), solver->get_is_propagated_constant(name(cmp)), solver->get_comes_from_non_annotated(name(cmp)) );


	//solver->print_path_stack();
	
	
	static int n;

	if(options->cmd_option_bool("follow_path") ){

		printf("follow_path\n");

		string path = options->cmd_option_str("path");
		int length = path.length();


		if(n < length){
			bool step = path[n] == 'T';
			printf("step %d\n", step);
			solver->push_path_stack(step);

			if( !solver->get_is_propagated_constant(name(cmp)) ){
				solver->push_condition_var(name(cmp),!step);
			}
			solver->push_condition_static_var(name(cmp),!step);
			n++;
			return step;
		}
	}

	if(options->cmd_option_bool("single_step") /*&& !solver->get_is_propagated_constant(name(cmp))*/){
		srand(clock());

		printf("single_step %s\n", realvalue(cmp).c_str());

		string real_value_prev = realvalue(cmp);

		solver->save_state();


////////////////////
		

		bool step = (real_value_prev == "true");
		solver->push_path_stack(step);
		solver->set_sat(true);



		file_initializations = "file_initializations_" + itos(rand());
		solver->dump_file_initializations(file_initializations);

		solver->push_condition_var(name(cmp), !step);
		solver->push_condition_static_var(name(cmp),!step);


		database->insert_problem();
		database->insert_frontend_interface();




////////////////////
		solver->load_state();
////////////////////




		if( solver->get_is_propagated_constant(name(cmp)) && propagate_constants ){
			solver->set_sat(false);
			exit(0);
		}

		solver->push_condition_var(name(cmp), step);
		solver->push_condition_static_var(name(cmp), step);

		//solver->show_problem();
		solver->solve_problem();

		file_initializations = "file_initializations_" + itos(rand());
		solver->dump_file_initializations(file_initializations);

		database->insert_problem();

		if( solver->solvable_problem() ){

			solver->push_path_stack( real_value_prev != "true");

			database->insert_frontend_interface();

			debug && printf("\e[31m fin hijo sat \e[0m\n"); fflush(stdout);
		} else {
			debug && printf("\e[31m hijo unsat \e[0m\n"); fflush(stdout);
		}

////////////////////

			printf("exit\n");
			exit(0);


	}


	string real_value_prev = realvalue(cmp);

	fflush(stdout);

	database->check_database();

	if( int pid = fork() ){

		//debug && printf("padre pid %d pidhijo %d\n", getpid(), pid); fflush(stdout);

		
		int status;
		waitpid(pid, &status, 0);

		solver->push_path_stack( real_value_prev == "true");
		solver->print_path_stack();


		//solve_problem();
		solver->set_sat(true);
		database->insert_problem();

		if( options->cmd_option_bool("propagate_constants") && solver->get_is_propagated_constant(name(cmp)) ){

			if(options->cmd_option_bool("generate_uppaal_model") )
				uppaal->br_instr_cond(name(cmp), real_value_prev == "false");
			
			return real_value_prev == "true";
		}


		if(database->already_covered()) exit(0);

		solver->push_condition(name(cmp), actual_function, joints, false);

		if(options->cmd_option_bool("generate_uppaal_model") )
			uppaal->br_instr_cond(name(cmp), real_value_prev == "false");

		debug && printf("\e[31m proceso %d acaba de esperar \e[0m\n", getpid() ); fflush(stdout);

		return real_value_prev == "true";
	} else {

		if( solver->get_is_propagated_constant(name(cmp)) && propagate_constants ) exit(0);

		if( exit_on_insert ){
			system("killall final");
			assert(0 && "exit_on_insert");
		}


		solver->push_condition(name(cmp), actual_function, joints, true);


		if(options->cmd_option_bool("generate_uppaal_model") )
			uppaal->br_instr_cond(name(cmp), real_value_prev == "true");

		see_each_problem && solver->show_problem();

		solver->solve_problem();
		database->insert_problem();

		if( solver->solvable_problem() ){
			debug && printf("\e[31m hijo sat \e[0m\n"); fflush(stdout);

			solver->push_path_stack( real_value_prev != "true");
			solver->print_path_stack();

			if(database->already_covered()) exit(0);

			//solver->solve_problem();
			debug && printf("\e[31m fin hijo sat \e[0m\n"); fflush(stdout);
			return real_value_prev != "true";
		} else {
			debug && printf("\e[31m hijo unsat \e[0m\n"); fflush(stdout);
			//insert_problem();
			exit(0);
		}
	}


}

void force_free(int* a){

}

void Operators::Free_fn( char* _oplist ){

	string oplist = string(_oplist).substr(0, strlen(_oplist) - 1);

	solver->free_var(name(oplist));
	debug && printf("\e[31m FreeFn %s\e[0m\n", _oplist );

}

vector<string> Operators::name( vector<string> input, string fn_name ){

	vector<string> ret;

	for( vector<string>::iterator it = input.begin(); it != input.end(); it++ ){
		ret.push_back( name(*it, fn_name) );
	}
	

	return ret;

}

string Operators::name( string input, string fn_name ){

	if(input.substr(0,9) != "constant" UNDERSCORE &&
			input.substr(0,4) != "mem" UNDERSCORE &&
	 		input.substr(0,7) != "global" UNDERSCORE &&
			input.substr(0,9) != "function" UNDERSCORE )
		myReplace(input, UNDERSCORE, "underscore" );


	if( input.substr(0,7) == "global" UNDERSCORE ){
		string postfix = input.substr(7);
		//printf("postfix %s\n", postfix.c_str() );
		myReplace(postfix, UNDERSCORE, "underscore");
		input = string("global") + UNDERSCORE + postfix;

		//printf("globalname %s\n", input.c_str());
	}

	if(input.substr(0,8) == "function"){
		string postfix = input.substr(8);
		//printf("postfix %s\n", postfix.c_str() );
		myReplace(postfix, UNDERSCORE, "underscore");
		input = string("function") + UNDERSCORE + postfix;
	}

	if(input.find("constant") != string::npos ){
		return input;
		//int ini = 9;
		//string interm = input.substr(ini);
		//int len = interm.find(UNDERSCORE);
		//string final = interm.substr(0, len);

		//return final;
	} else if (input.substr(0,4) == "mem" UNDERSCORE ){
		return input;
	} else if (input.substr(0,7) == "global" UNDERSCORE ){
		return input;
	} else if (input.substr(0,8) == "function"){
		return input;
	} else {
		if(options->cmd_option_bool("recursive"))
			if(fn_name == ""){
				return crcstack() + UNDERSCORE + input;
			} else {
				return crcstack_name(fn_name) + UNDERSCORE + input;
			}

		else
			return ((fn_name == "")?actual_function:fn_name) + UNDERSCORE + input;
		//return input;
	}


}

string Operators::crcstack(){
	
	string all_stack;
	for( vector<pair<string, string> >::iterator it = callstack.begin(); it != callstack.end(); it++ ){
		string fnname = it->second;
		all_stack += fnname;
	}

	long crc = rc_crc32(0, all_stack.c_str(), all_stack.length());

	return all_stack;
	return itos(abs(crc));
	
}


string Operators::crcstack_name(string fn_name){
	
	string all_stack;
	for( vector<pair<string, string> >::iterator it = callstack.begin(); it != callstack.end(); it++ ){
		string fnname = it->second;
		all_stack += fnname;
	}
	all_stack += fn_name;

	long crc = rc_crc32(0, all_stack.c_str(), all_stack.length());

	return all_stack;
	return itos(abs(crc));
	
}


void Operators::set_name_hint(string name, string hint){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_name_hint");
	solver->set_name_hint(name, hint);

}

bool Operators::check_mangled_name(string name){

	//printf("check mangled name %s\n", name.c_str());
	int number_of_underscore = count(name, UNDERSCORE);
	if(
			number_of_underscore != 2 && // constant_IntegerTyID32_3
			number_of_underscore != 1 && // main_registerunderscoreval mem_9
			number_of_underscore != 0    // 0
	)
		return false;

	if( number_of_underscore == 1 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if(tokens[1].substr(0,8) != "register" &&
		   tokens[0].substr(0,3) != "mem"      &&
		   tokens[0].substr(0,6) != "global"   &&
		   tokens[0].substr(0,8) != "function"
		  ) return false;
	}

	if( number_of_underscore == 2 ){
		vector<string> tokens = tokenize(name, UNDERSCORE);
		if( tokens[0] != "constant" ){
			return false;
		}
	}

	if( number_of_underscore  == 0 ){
		if( !is_number(name) )
			return false;
	}


	return true;

}

string Operators::realvalue(string varname){
	return solver->realvalue(name(varname));
}

int Operators::get_offset(vector<string> indexes, string offset_tree, string* remaining_tree){


	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[33m %s ", it->c_str() );
	} debug && printf(" --- ");
	debug && printf(" offset %s\e[0m\n", offset_tree.c_str() );
	

	string realvalue_index_0_s = realvalue( indexes[0] );

	debug && printf("\e[33m %s %s \e[0m\n", indexes[0].c_str(), realvalue(indexes[0]).c_str() );

	int realvalue_index_0 = stoi(realvalue_index_0_s);

	if( has_index(offset_tree, realvalue_index_0) ){

		int ini_elem = get_ini_elem(realvalue_index_0, offset_tree);
		string right_str = offset_tree.substr(ini_elem);
		string elem_str = close_str(right_str);
		//printf("elem_str %s\n", elem_str.c_str());

		vector<string>::iterator first_it = indexes.begin(); first_it++;
		vector<string> rem_indexes = vector<string>(first_it, indexes.end());

		if( rem_indexes.size() ){
			return get_offset(rem_indexes, elem_str, remaining_tree);
		} else {
			*remaining_tree = offset_tree;
			//printf("elem_str to trim %s\n", elem_str.c_str());
			return stoi(trimpar(elem_str));
		}

	} else {
		vector<string> tokens = tokenize(offset_tree, "(),");
		string size_s = tokens[tokens.size()-1];
		int size = stoi(size_s);
		printf("offset_tree %s realvalue_index_0 %d size_s %s\n", offset_tree.c_str(), realvalue_index_0, size_s.c_str());
		return size*realvalue_index_0;
	}

}

string Operators::get_actual_bb(){

	return actual_bb;

}

string Operators::get_actual_function(){
	return actual_function;
}

void Operators::memcpy(char* _addr_dst, char* _addr_src, char* _size_bytes, char* _align, char* _is_volatile){

	string addr_dst = string(_addr_dst);
	string addr_src = string(_addr_src);
	string size_bytes = string(_size_bytes);
	string align = string(_align);
	string is_volatile = string(_is_volatile);

	int addr_src_i = stoi(solver->realvalue(name(addr_src)));
	int addr_dst_i = stoi(solver->realvalue(name(addr_dst)));
	int n_elems = stoi(solver->realvalue(size_bytes))/stoi(solver->realvalue(align));
	int align_i = stoi(solver->realvalue(align));


	for ( unsigned int mem_src = addr_src_i, mem_dst = addr_dst_i; n_elems > 0; mem_src += align_i, mem_dst += align_i, n_elems--) {
		string mem_name_src = "mem_" + itos(mem_src);
		string mem_name_dst = "mem_" + itos(mem_dst);
		solver->assign_instruction(mem_name_src,mem_name_dst);
	}

	//printf("addr_dst_i %d\n", addr_dst_i);
	//printf("n_elems %d\n", n_elems);
	

	printf("\e[31m llvm.memcpy \e[31m addr_dst \e[0m %s \e[31m addr_src \e[0m %s \e[31m size_bytes \e[0m %s \e[31m align \e[0m %s \e[31m is_volatile \e[0m %s\n", addr_dst.c_str(), addr_src.c_str(), size_bytes.c_str(), align.c_str(), is_volatile.c_str());
	//exit(0);
	
}

void Operators::assume(char* _assumption_register){

	string assumption_register = string(_assumption_register);

	printf("assume %s %s %s\n", assumption_register.c_str(), solver->content_smt(name(assumption_register)).c_str(), solver->realvalue(name(assumption_register)).c_str() );

	if( solver->get_is_propagated_constant(name(assumption_register)) || solver->is_constant(name(assumption_register)) ){
		if(solver->realvalue(name(assumption_register)) == "true") return;
		if(solver->realvalue(name(assumption_register)) == "1") return;

		printf("Assumption is false\n");
		//exit(0);
		//assert(0 && "Assumption is false");
	}



	solver->push_condition_var(name(assumption_register));

	if(solver->realvalue(name(assumption_register)) == "false") solver->solve_problem();
	if(solver->realvalue(name(assumption_register)) == "0"    ) solver->solve_problem();

	debug && printf("\e[31m assume %s %s \e[0m\n", assumption_register.c_str(), solver->debug_content(name(assumption_register)).c_str() );

}


void Operators::assertion(char* _assertion_register){

	string assertion_register = string(_assertion_register);

	if(int pid = fork()){
		int status; waitpid(pid, &status, 0);
	} else {
		solver->push_condition_var(name(assertion_register), true);
		solver->solve_problem();
		if(solver->solvable_problem()){
			database->insert_assertion();
			printf("Assertion fired \n");
		}
		exit(0);
	}
	
	debug && printf("\e[31m assertion %s %s \e[0m\n", assertion_register.c_str(), solver->debug_content(name(assertion_register)).c_str() );

}


void Operators::checkerror_bb(char* name){

	if(!name) return;

	//printf("checkerror %s\n", name);

	//if( string(name) == options->cmd_option_str("target_node") ){
	if( string(name).substr(0,5) == "ERROR" || string(name) == "__VERIFIER_assert.exit" ){
		printf("ERROR_HIT\n");
		exit(0);
	}

}


void Operators::checkerror_fn(char* name){

	if(!name) return;
	//printf("checkerror %s\n", name);

	//if( string(name) == options->cmd_option_str("target_node") ){
	if( string(name) == "__VERIFIER_error" ){
		printf("ERROR_HIT\n");
		exit(0);
	}

}


void* Operators::fp_hook(char* _register_name){

	string register_name = string(_register_name);

	string caller = actual_function;
	string var = name(register_name, caller);
	string pointedfn = solver->realvalue_mangled(name(register_name,caller));
	printf("\e[36m operators_fp_hook \e[0m caller %s var %s pointed %s register_name %s\n", caller.c_str(), var.c_str(), pointedfn.c_str(), register_name.c_str() );
	register_name = solver->realvalue_mangled(var);
	if(register_name.substr(0,9) == "constant_"){
		register_name = "function"+register_name.substr(22);
		myReplace(register_name, "underscore", "");
	} else {
		register_name = realvalue("mem_" + register_name);
	}

	printf("register_name %s %d\n", register_name.c_str(), register_name.length());

	if(register_name.substr(0,8) == "function"){
		pointedfn = pointedfn;
	} else if(register_name.substr(0,22) == "constant_FunctionTyID_"){
		pointedfn = register_name.substr(22);
	} else {
		assert(0 && "This is not a function");
	}

	myReplace(pointedfn, "constant_FunctionTyID_", "");
	myReplace(pointedfn, "underscore", "_");
	myReplace(pointedfn, "function", "");

	printf("objdump for function %s", ("objdump -t " + tmp_file("final") + " | grep " + pointedfn + " | cut -d\" \" -f1 > " + tmp_file("function_addr")).c_str());

	system(("objdump -t " + tmp_file("final") + " | grep " + pointedfn + " | cut -d\" \" -f1 > " + tmp_file("function_addr")).c_str());

	unsigned int ret;

	FILE* file = fopen(tmp_file("function_addr").c_str(), "r");
	fscanf(file, "%x", &ret);
	fclose(file);

	return (void*)ret;

}


