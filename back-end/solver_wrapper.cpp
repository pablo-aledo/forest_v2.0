/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/12/2013 02:38:08 PM
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


#include "solver_wrapper.h"
#include <sys/wait.h>
#include "operators.h"
#include "utils.h"
#include "timer.h"
#include "options.h"
#include "database.h"
#include "uppaal.h"
#include "architecture.h"

#define UNDERSCORE "_"
#define PAUSE_ON_INSERT false
#define EXIT_ON_INSERT false
#define check_mangled_name(A) operators->check_mangled_name(A)

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;
extern Uppaal* uppaal;

SolverWrapper::SolverWrapper(){

	options->read_options();
	debug = options->cmd_option_bool("verbose");
	isdriver = 0;

}

void SolverWrapper::set_isdriver(){
	isdriver = true;
}

SolverWrapper::~SolverWrapper(){}

void SolverWrapper::free_var(string var){

	if(!check_mangled_name(var)) assert(0 && "Wrong name for content");

	stringstream mem_name; mem_name << "mem_" << realvalue(var);
	forced_free_vars.insert( mem_name.str() );

}


string SolverWrapper::find_mem_of_id(string id){


	for( map<string,Variable>::iterator it = variables_generic.begin(); it != variables_generic.end(); it++ ){
		if(it->second.name_hint == id){
			return it->first;
		}
	}

	return "";
	
	

}

void SolverWrapper::show_check_sat(){


	printf("(check-sat)\n");

}

void SolverWrapper::show_header(){

	printf("(set-option :produce-models true)\n");
	printf("(set-option :pp-decimal true)\n");
	printf("(set-logic AUFNIRA)\n");

}

void SolverWrapper::show_tail(){

	printf("(exit)\n");
}

void SolverWrapper::show_assigns(){


	printf("SolverWrapper::show_assigns\n");

	for( map<string,Variable>::iterator it = variables_generic.begin(); it != variables_generic.end(); it++ ){
		string name = it->first;
		string value = it->second.real_value;

		//printf("\e[32m name \e[0m %s \e[32m value \e[0m %s \e[32m expression \e[0m %s\n", name.c_str(), value.c_str(), content_smt(name).c_str());
		printf("\e[32m name \e[0m %s \e[32m expression \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), content_smt(name).c_str(), value.c_str());

	}
	

}

int SolverWrapper::get_num_fvars(){


	return free_variables.size();

}


void SolverWrapper::set_real_value(string varname, string value){

	//printf("set_real_value %s %s\n", varname.c_str(), value.c_str()); fflush(stdout);
	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	if(value.substr(0,2) == "#x") assert(0 && "internal real value");
	if(!is_number(value) && !is_function(value)){ printf("varname %s value %s\n", varname.c_str(), value.c_str() ); assert(0 && "Not a Number"); };

	variables_generic[varname].real_value = value;
}

void SolverWrapper::initialize_real_value(string varname, string varhint){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	printf("initializerealvalue %s %s %s %s\n", varname.c_str(), varhint.c_str(), variables_generic[varname].real_value.c_str(), initializations[varhint].c_str() );

	//if(variables_generic[varname].real_value == "")
		//variables_generic[varname].real_value = "0";

	if( initializations[varhint] != "" ){
		printf("take initialization %s\n", initializations[varhint].c_str());
		variables_generic[varname].real_value = initializations[varhint];
	} else {
		variables_generic[varname].real_value = "0";
	}

}

void SolverWrapper::set_real_value_mangled(string varname, string value ){


	if(!check_mangled_name(varname)) assert(0 && "Wrong name for set_real_value");

	variables_generic[varname].real_value = value;
}

void SolverWrapper::set_real_value_hint(string hint, string value ){



	printf("set_real_value_hint %s %s\n", hint.c_str(), value.c_str());

	
	for( map<string,Variable>::iterator it = variables_generic.begin(); it != variables_generic.end(); it++ ){
		if(it->second.name_hint == hint){
			it->second.real_value = value;
			return;

		}
			
	}

	assert(0 && "Variable not found");
	
}


float SolverWrapper::get_solve_time(){
	return spent_time;
}



void SolverWrapper::check_name_and_pos(string name, string position){
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		if(it->position == position && it->name != name) assert(0 && "Duplicated entry in free_variables");
		if(it->name == name && it->position != position) assert(0 && "Duplicated entry in free_variables");
	}
	
}

void check_name_does_not_exist(set<NameAndPosition> free_variables, string name){
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		if(it->name == name){
			printf("repeated name\n");
			assert(0 && "repeated name");
		}
	}
	
}


void SolverWrapper::insert_variable(string name, string position){

	if( name == "" ){ printf("Empty name %s\n", name.c_str()); assert(0); }
	if( position == "" ){ printf("Empty position %s\n", position.c_str()); assert(0 && "Empty position"); }
	if( variables_generic[name].type == "Pointer" ) printf("Pointer_free_variable\n");
	if( variables_generic[name].type == "PointerTyID" ) printf("Pointer_free_variable\n");

	if(!check_mangled_name(name)) assert(0 && "Wrong name for insert_variable");


	if( name.find("constant") != string::npos )
		return;

	if( is_number(name) )
		return;


	if( name.find("function") != string::npos )
		return;

	if( gettype(name) == "Function" )
		return;

		
	debug && printf("\e[35m Insert_variable \e[0m name %s hint %s position %s size %lu\n", name.c_str(), variables_generic[name].name_hint.c_str(), position.c_str(), free_variables.size() );

	if( PAUSE_ON_INSERT )
		getchar();

	if( EXIT_ON_INSERT )
		exit(0);

	//check_name_and_pos(name, position);

	if(variables_generic[name].real_value != ""){
		NameAndPosition nandp = {name, position, realvalue(name)};
		assert(position != "" && "Empty variable name");
		free_variables.insert(nandp);
	} else {
		NameAndPosition nandp = {name, position};
		assert(position != "" && "Empty variable name");
		free_variables.insert(nandp);
	}
	//check_name_does_not_exist(free_variables, name);
	database->insert_variable(name);

	//for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
	//	printf("free_variable %s %s\n", it->name.c_str(), it->position.c_str() );
	//}
	

}


void SolverWrapper::push_condition(string name, string actual_function, vector<string> joints, bool invert){

	if( (!invert && realvalue(name) == "true") || (invert && realvalue(name) == "false") ){
		push_condition_var(name);
	} else if( (!invert && realvalue(name) == "false") || (invert && realvalue(name) == "true") ){
		push_condition_var(name, true);
	} else {
		assert(0 && "Non-boolean value for condition");
	}
}

string SolverWrapper::negateop(string predicate){

	if( predicate == "#"  )  return "=";
	if( predicate == "="  )  return "#";
	if( predicate == ">"  )  return "<=";
	if( predicate == ">=" )  return "<";
	if( predicate == "<"  )  return ">=";
	if( predicate == "<=" )  return ">";
	if( predicate == "u>"  ) return "u<=";
	if( predicate == "u>=" ) return "u<";
	if( predicate == "u<"  ) return "u>=";
	if( predicate == "u<=" ) return "u>";
	assert(0 && "Unknown Operation");

}

string SolverWrapper::name_without_suffix( string name ){


	if(!check_mangled_name(name)) assert(0 && "Wrong name for name_without_suffix");

	int s1 = name.find(UNDERSCORE);
	int s2 = name.find(UNDERSCORE, s1+1);
	return name.substr(0,s2);
}


void SolverWrapper::set_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for set_comes_from_non_annotated");

	debug && printf("\e[32m set_comes_from_non_annotated \e[0m %s \n", name.c_str() );

	variables_generic[name].comes_from_non_annotated = true;
	
	
}

bool SolverWrapper::get_comes_from_non_annotated(string name){

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for get_comes_from_non_annotated");

	return variables_generic[name].comes_from_non_annotated;
	
	
}

string SolverWrapper::realvalue_mangled(string varname){


	//printf("\e[33m realvalue_mangled \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue_mangled");


	if( varname.find("constant") != string::npos ){
		return varname.substr(9);
	} else if( variables_generic[varname].real_value == "" ){
		return "0";
	} else {
		return variables_generic[varname].real_value;
	}
}

string SolverWrapper::realvalue(string varname){


	printf("\e[33m realvalue \e[0m %s\n", varname.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for realvalue");

	if(is_number(varname)){
		assert(0 && "Real-value of single number");
	} else if( is_function(varname) ){
		//printf("function %s\n", varname.c_str() );
		return varname;
	} else if( is_constant(varname) ){
		printf("constant %s\n", varname.c_str());
		return tokenize(varname, "_")[2];
	} else if( variables_generic[varname].real_value == "" ){
		printf("varname %s\n", varname.c_str());
		assert(0 && "Real-value of empty");
	}else{
		//printf("else\n");
		if( variables_generic.find(varname) == variables_generic.end() ){
			assert(0 && "Variable not found");
		}
		//printf("else %s\n", variables_generic[varname].real_value.c_str());
		return variables_generic[varname].real_value;
	}

}

void SolverWrapper::set_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for set_is_propagated_constant");

	variables_generic[varname].is_propagated_constant = true;

}

void SolverWrapper::unset_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for unset_is_propagated_constant");

	variables_generic[varname].is_propagated_constant = false;

}

bool SolverWrapper::is_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for is_constant");

	return varname.substr(0,9) == "constant" UNDERSCORE;

}

bool SolverWrapper::is_forced_free(string position, bool colateral_effect){


	bool ret;

	if(!check_mangled_name(position)) assert(0 && "Wrong src for is_forced_free");

	if(colateral_effect){


		if( forced_free_vars.find(position) != forced_free_vars.end() ){
			if( already_forced_free.find(position) != already_forced_free.end() ){
				ret = false;
			} else{
				already_forced_free.insert(position);
				ret = true;
			}
		} else {
			ret = false;
		}

	} else {

		if( forced_free_vars.find(position) != forced_free_vars.end() ){
			ret = true;
		} else {
			ret = false;
		}

	}


	//printf("SolverWrapper::is_forced_free %s %d : %d. size %lu\n", position.c_str(), colateral_effect, ret, forced_free_vars.size());


	return ret;
}

void SolverWrapper::load_forced_free_vars(){


	ifstream input("free_vars");
	string line;
	
	while( getline( input, line ) ) {
		forced_free_vars.insert(line);
	}
	
}

void SolverWrapper::load_forced_free_hints(){


	ifstream input("free_hints");
	string line;
	
	while( getline( input, line ) ) {
		forced_free_hints.insert(line);
	}
	
}

bool SolverWrapper::is_forced_free_hint(string hint){
	//printf("is_forced_free_hint %s\n", hint.c_str());
	return  forced_free_hints.find(hint) != forced_free_hints.end();
}

void SolverWrapper::insert_forced_free_var(string name){
	printf("insert_forced_free_var %s\n", name.c_str());
	forced_free_vars.insert(name);
}

void SolverWrapper::set_first_content_value(string var, string value){
	printf("\e[36m set_first_content_value %s %s\e[0m\n", var.c_str(), value.c_str() );
	first_content_value[var] = value;
}

string SolverWrapper::get_first_content_value(string var){
	return first_content_value[var];
}


bool SolverWrapper::implemented_operation(string operation){

	if(operation == "<=") return true;
	if(operation == ">=") return true;
	if(operation == "<" ) return true;
	if(operation == ">" ) return true;
	if(operation == "u<=") return true;
	if(operation == "u>=") return true;
	if(operation == "u<" ) return true;
	if(operation == "u>" ) return true;
	if(operation == "=" ) return true;
	if(operation == "#" ) return true;
	if(operation == "+" ) return true;
	if(operation == "-" ) return true;
	if(operation == "*" ) return true;
	if(operation == "/" ) return true;
	if(operation == "%" ) return true;
	if(operation == "u%" ) return true;
	if(operation == "R" ) return true;
	if(operation == "L" ) return true;
	if(operation == "Y" ) return true;
	if(operation == "O" ) return true;
	if(operation == "X" ) return true;

	printf("operation %s\n", operation.c_str());
	return false;
}

bool SolverWrapper::is_free_var(string name){
	if(!check_mangled_name(name)) assert(0 && "Wrong name for is_free_var");

	//printf("is_free_var %s %s ", name.c_str(), get_name_hint(name).c_str());

	if(get_name_hint(name).substr(0,7) == "global_" && options->cmd_option_bool("globals_always_free")){ printf("1\n");return true;}

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		if(it->name == name){ /*printf("1\n");*/ return true;}
	}

	//printf("0\n");
	return false;
	
}

bool SolverWrapper::get_is_propagated_constant(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for get_is_propagated_constant");
	if(is_forced_free(varname, false)) return false;
	return variables_generic[varname].is_propagated_constant;
}

string SolverWrapper::gettype(string name){

	//printf("gettype %s\n", name.c_str());

	if( name.substr(0,9) == "constant_" ){
		//assert(tokenize(name, "_")[1] != "" && "empty gettype");
		return tokenize(name, "_")[1];
	}

	if( isdriver && variables_generic.find(name) == variables_generic.end() ) assert(0 && "Not such variable");

	//assert(variables_generic[name].type != "" && "empty gettype");
	return variables_generic[name].type;
}

void SolverWrapper::set_name_hint(string name, string hint){

	debug && printf("\e[35m set_name_hint \e[0m name %s hint %s \n", name.c_str(), hint.c_str() );

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_name_hint");

	variables_generic[name].name_hint = hint;
}

string SolverWrapper::get_name_hint(string name){

	//debug && printf("\e[33m get_name_hint %s %s\e[0m\n", name.c_str(), variables_generic[name].name_hint.c_str() );

	return variables_generic[name].name_hint;
}

string SolverWrapper::find_by_name_hint(string hint){

	myReplace(hint, "underscore", "_");
	string suffix = hint.substr(hint.find("_") + 1);
	string prefix = hint.substr(0,hint.find("_"));
	//myReplace(suffix, "_", "underscore");
	hint = prefix + "_" + suffix;

	//printf("variables_generic.size %lu\n", variables_generic.size());

	for( map<string,Variable>::iterator it = variables_generic.begin(); it != variables_generic.end(); it++ ){

		//printf("find_by_name_hint %s %s\n", it->first.c_str(), it->second.name_hint.c_str());

		if(it->second.name_hint == hint )
		//if(it->first == hint)
			return it->first;
	}
	
	printf("hint not found %s\n", hint.c_str());
	assert(0 && "name not found");

	return "";
	
}

void SolverWrapper::settype(string name, string type){

	// debug && printf("\e[32m Settype \e[0m. %s %s\n", name.c_str(), type.c_str() );

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for settype");
	variables_generic[name].type = type;

}

string SolverWrapper::get_type(string name){

	//printf("get_type %s\n", name.c_str());

	if( !check_mangled_name(name) ) assert(0 && "Wrong name for type");

	if(name.substr(0,8) == "function"){
		return "Function";
	}

	if(name.substr(0,9) == "constant" UNDERSCORE) return "IntegerTyID32";
	if( is_number(name) ){

		if( name.find(".") != string::npos )
			return "FloatTyID";
		else
			return "IntegerTyID32";
	}

	if (gettype(name) == "IntegerTyID32")
		return "Int";

	if (gettype(name) == "DoubleTyID")
		return "Real";

	if (gettype(name) == "IntegerTyID64")
		return "Int";

	if (gettype(name) == "IntegerTyID8")
		return "Int";

	if (gettype(name) == "IntegerTyID16")
		return "Int";

	if (gettype(name) == "PointerTyID")
		return "Int";

	if (gettype(name) == "Int")
		return "Int";

	if (gettype(name) == "FloatTyID")
		return "Real";

	if (gettype(name) == "Real")
		return "Real";

	if (gettype(name) == "bool")
		return "bool";

	if (gettype(name) == "Pointer")
		return "Pointer";

	if (gettype(name) == "Function")
		return "Function";


	printf("name %s type %s\n", name.c_str(), gettype(name).c_str() );

	if(isdriver) assert(0 && "Unknown Type");

	return "Int";

}

vector<bool> SolverWrapper::get_path_stack(){

	return path_stack;
}

string SolverWrapper::get_path_stack_str(){

	string ret;
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		if(*it)
			ret += "T";
		else
			ret += "F";
	}
	
	return ret;
}

void SolverWrapper::push_path_stack(bool step){

	path_stack.push_back(step);
}

void SolverWrapper::print_path_stack(){



	printf("\e[33m Path_stack \e[0m");
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		printf("%s", (*it)?"T":"F" );
	}
	printf("\n");

	printf("\e[33m Depth \e[0m %lu\n", path_stack.size());
	

}

map<string, Variable> SolverWrapper::get_map_variables(){

	return variables_generic;
}

string SolverWrapper::get_comma_stack_conditions_static(){

	stringstream ret;

	for( vector<string>::iterator it = conditions_static.begin(); it != conditions_static.end(); it++ ){
		string condition = *it;
		ret << condition << ",";
	}


	return ret.str();

}


set<NameAndPosition> SolverWrapper::get_free_variables(){
	return free_variables;
}

string SolverWrapper::get_position(string name){


	return variables_generic[name].name_hint;

}

vector<int> SolverWrapper::jump_offsets(string offset_tree){

	vector<int> ret;

	for ( unsigned int i = 1; offset_tree[i] == '('; i++) {
		string sub = close_str(offset_tree.substr(i));
		string right = sub.substr(sub.find_last_of(","));
		string center = right.substr(1,right.length()-2);
		//printf("sub %s %s\n", sub.c_str(), center.c_str() );
		ret.push_back(stoi(center));
	}

	return ret;
}

set<set<pair<string, int> > > SolverWrapper::get_exclusions( map<set<pair<string, int> > , int > solutions ){

	set<set<pair<string, int> > > ret;
	
	for( map<set<pair<string, int> > , int >::iterator it = solutions.begin(); it != solutions.end(); it++ ){
		set<pair<string, int> > sol = it->first;
		ret.insert(sol);
	}

	return ret;
	

}

void SolverWrapper::propagate_binary(string op1, string op2, string dst){


	unset_is_propagated_constant(dst);

	if( get_is_propagated_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( get_is_propagated_constant(op1) && is_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if( is_constant(op1) && get_is_propagated_constant(op2) ){
		set_is_propagated_constant(dst);
	}

	if(is_free_var(op1) || is_free_var(op2))
		unset_is_propagated_constant(dst);


	if( get_comes_from_non_annotated(op1) )
		set_comes_from_non_annotated(dst);

	if( get_comes_from_non_annotated(op2) )
		set_comes_from_non_annotated(dst);

	set_last_address(dst, get_last_address(op1));
	set_first_address(dst, get_first_address(op1));


	if( variables_generic[op1].malloc_origin != ""){
		settype(variables_generic[op1].malloc_origin, gettype(op2));
	}



	propagate_binary_extra(op1, op2, dst);
}

void SolverWrapper::set_malloc_origin(string name, string malloc_origin){
	variables_generic[name].malloc_origin = malloc_origin;
}

void SolverWrapper::propagate_unary(string src, string dst, bool forcedfree){


	if( (get_is_propagated_constant(src) || is_constant(src)) && !forcedfree )
		set_is_propagated_constant(dst);
	else
		unset_is_propagated_constant(dst);

	if(is_free_var(src))
		unset_is_propagated_constant(dst);

	if(get_comes_from_non_annotated(src))
		set_comes_from_non_annotated(dst);

	assert(get_last_address(src) >= get_first_address(src));

	set_last_address(dst, get_last_address(src));
	set_first_address(dst, get_first_address(src));

	if(variables_generic[src].malloc_origin != "")
		variables_generic[dst].malloc_origin = variables_generic[src].malloc_origin;


	propagate_unary_extra(src, dst, forcedfree );


}

bool has_maxval(string type){

	if(type == "FloatTyID") return false;
	if(type == "DoubleTyID") return false;

	return true;

}

bool has_minval(string type){

	if(type == "FloatTyID") return false;

	return true;
}

void SolverWrapper::cast_instruction(string src, string dst, string type_src, string type_dst, string sext){

	assign_instruction(src,dst);

	if(is_function(src)) return;

	cast_instruction_content(src, dst, type_src, type_dst, sext);

	if( bits(type_dst) < bits(type_src) ){
		set_real_value(dst, trunc(realvalue(src), type_dst) );
	} else {
		set_real_value(dst, realvalue(src));
	}

}

void SolverWrapper::binary_instruction(string dst, string op1, string op2, string operation){

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for binary_instruction");
	if(!check_mangled_name(op1)) assert(0 && "Wrong op1 for binary_instruction");
	if(!check_mangled_name(op2)) assert(0 && "Wrong op2 for binary_instruction");
	if(!implemented_operation(operation)){ printf("not implemented operation %s\n", operation.c_str());  assert(0 && "Not implemented operation"); }

	debug && printf("\n\e[32m Binary_instruction %s = %s %s %s (%s %s)\e[0m\n",
			dst.c_str(),op1.c_str(), operation.c_str(),op2.c_str(),
		        get_type(op1).c_str(), get_type(op2).c_str() );



	if( variables_generic[op1].type != "" )
		settype(dst, get_type(op1));
	else
		settype(dst, get_type(op2));


	binary_instruction_content(dst, op1, op2, operation);

	if( operation == "#" ){ // neq_operation
		string value_1_s = make_unsigned(realvalue(op1), gettype(op1));
		string value_2_s = make_unsigned(realvalue(op2), gettype(op2));
		int value_1;
		int value_2;

		if(value_1_s == "true"){
			value_1 = 1;
		} else if(value_1_s == "false"){
			value_1 = 0;
		} else {
			value_1 = stoi(value_1_s);
		}

		if(value_2_s == "true"){
			value_2 = 1;
		} else if(value_2_s == "false"){
			value_2 = 0;
		} else {
			value_2 = stoi(value_2_s);
		}

		set_real_value(dst, ( value_1 != value_2 )?"true":"false" );
	} else if (operation == "%") { // rem_operator
		if(stoi(realvalue(op2)) == 0){
			database->insert_remzero();
			printf("Remainder by 0\n");
			exit(0);
		}
		stringstream result; result << stoi(realvalue(op1)) % stoi(realvalue(op2));
		set_real_value(dst, result.str());
	} else if (operation == "u%") { // rem_operator
		if(stoi(realvalue(op2)) == 0){
			database->insert_remzero();
			printf("Remainder by 0\n");
			exit(0);
		}
		stringstream result; result << (unsigned int)stoi(realvalue(op1)) % (unsigned int)stoi(realvalue(op2));
		set_real_value(dst, result.str());
	} else if (operation == "R" ) { // right_shift
		int places = stoi( realvalue(op2) );
		int result_i = (unsigned int)stoi(realvalue(op1)) >> places;
		stringstream result; result << result_i;
		set_real_value(dst, result.str());
	} else if (operation == "L" ) { // left_shift
		int places = stoi( realvalue(op2) );
		int result_i = stoi(realvalue(op1)) << places;
		stringstream result; result << result_i;
		set_real_value(dst, result.str());
	} else if (operation == "Y" ) { // and_operation
		int result_i = (unsigned int)stoi(realvalue(op1)) & (unsigned int)stoi(realvalue(op2));
		stringstream result; result << result_i;
		set_real_value(dst, result.str());
	} else if (operation == "O" ) { // or_operation
		int result_i = (unsigned int)stoi(realvalue(op1)) | (unsigned int)stoi(realvalue(op2));
		stringstream result; result << result_i;
		set_real_value(dst, result.str());
	} else if (operation == "X" ) { // xor_operation
		stringstream result;
		if( get_type(dst) == "Real" ){
			assert(0 && "Xor of two reals");
		} else if (get_type(dst) == "Int") {
			result << (stoi(realvalue(op1)) ^ stoi(realvalue(op2)));
		} else if(get_type(dst) == "bool"){
			result << (stoi(realvalue(op1)) ^ stoi(realvalue(op2)));
		} else if( get_type(dst) == "Pointer" ) {
			assert(0 && "Xor of two pointers");
		} else {
			printf("Type %s\n", gettype(dst).c_str());
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
	} else if(operation == "<="){ // leq_operation
		set_real_value(dst, ( stoi(realvalue(op1) ) <= stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == ">="){ // geq_operation
		set_real_value(dst, ( stoi(realvalue(op1) ) >= stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "<"){ // lt_operation
		set_real_value(dst, ( stoi(realvalue(op1) ) < stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == ">"){ // bt_operation
		set_real_value(dst, ( stoi(realvalue(op1) ) > stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "u<="){
		set_real_value(dst, ( (unsigned int)stoi(realvalue(op1) ) <= (unsigned int)stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "u>="){
		set_real_value(dst, ( (unsigned int)stoi(realvalue(op1) ) >= (unsigned int)stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "u<"){
		set_real_value(dst, ( (unsigned int)stoi(realvalue(op1) ) <  (unsigned int)stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "u>"){
		set_real_value(dst, ( (unsigned int)stoi(realvalue(op1) ) >  (unsigned int)stoi( realvalue(op2) ) )?"true":"false" );
	} else if(operation == "="){ // eq_operation
		//printf("realvalueop1 %s realvalueop2 %s\n", realvalue(op1).c_str(), realvalue(op2).c_str());
		//string rv1 = make_unsigned(realvalue(op1), gettype(op1));
		//string rv2 = make_unsigned(realvalue(op2), gettype(op2));
		//printf("realvalueop1u %s realvalueop2u %s\n", rv1.c_str(), rv2.c_str());
		string rv1 = realvalue(op1);
		string rv2 = realvalue(op2);

		if(rv1 == "true") rv1 = "1"; if(rv1 == "false") rv1 = "0";
		if(rv2 == "true") rv2 = "1"; if(rv2 == "false") rv2 = "0";

		set_real_value(dst, (stoi(rv1) == stoi(rv2))?"true":"false" );
	} else if(operation == "+"){ // add_operation
		stringstream result;
		if( get_type(dst) == "Real" ){
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else if (get_type(dst) == "Int") {
			result << stoi(realvalue(op1)) + stoi(realvalue(op2));
		} else if( get_type(dst) == "Pointer" ) {
			result << stof(realvalue(op1)) + stof(realvalue(op2));
		} else {
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
	} else if(operation == "-"){ // sub_operation
		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) - stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) - stoi(realvalue(op2));
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	} else if(operation == "*"){ // mul_operation

		stringstream result;
		if( get_type(dst) == "Real" )
			result << stof(realvalue(op1)) * stof(realvalue(op2));
		else if (get_type(dst) == "Int")
			result << stoi(realvalue(op1)) * stoi(realvalue(op2)), gettype(op1);
		else
			assert(0 && "Unknown type");


		set_real_value(dst, result.str());
	} else if(operation == "/"){ // div_operation
		stringstream result;
		if( get_type(dst) == "Real" ){



			if(stof(realvalue(op2)) == 0.0){
				database->insert_divzero();
				printf("Division by 0\n");
				exit(0);
			}

			if(int pid = fork()){
				int status; waitpid(pid, &status, 0);
				add_neq_zero(op2);
			} else {
				add_eq_zero(op2);
				solve_problem();
				if(solvable_problem()){
					database->insert_divzero();
					printf("Division by 0\n");
				}
				exit(0);
			}

			result << stoi(realvalue(op1)) / stoi(realvalue(op2));




			result << stof(realvalue(op1)) / stof(realvalue(op2));
		} else if (get_type(dst) == "Int") {
			if(stoi(realvalue(op2)) == 0){
				database->insert_divzero();
				printf("Division by 0\n");
				exit(0);
			}

			if(int pid = fork()){
				int status; waitpid(pid, &status, 0);
				add_neq_zero(op2);
			} else {
				add_eq_zero(op2);
				solve_problem();
				if(solvable_problem()){
					database->insert_divzero();
					printf("Division by 0\n");
				}
				exit(0);
			}

			result << stoi(realvalue(op1)) / stoi(realvalue(op2));
		} else {
			assert(0 && "Unknown type");
		}

		set_real_value(dst, result.str());
	} else {
		printf("operator %s\n", operation.c_str());
		assert(0 && "Unknown Operator");
	}











	propagate_binary(op1, op2, dst);

	if( variables_generic[op1].type != "" ) variables_generic[dst].type = variables_generic[op1].type;
	if( variables_generic[op2].type != "" ) variables_generic[dst].type = variables_generic[op2].type;


	if(
		operation == "#" ||
		operation == "<=" ||
		operation == "u<=" ||
		operation == ">=" ||
		operation == "<" ||
		operation == ">" ||
		operation == "="
	  ){
		settype(dst, "bool");
	}


	make_signed(dst, gettype(dst));

	//if( has_maxval(gettype(dst)) && stoi(realvalue(dst)) > maxval(gettype(dst)) ){
		//int realval = stoi(realvalue(dst));
		//realval = realval % maxval(gettype(dst));
		//set_real_value(dst, itos(realval));
	//}


	//if( has_minval(gettype(dst)) && stoi(realvalue(dst)) < minval(gettype(dst)) ){
		//int realval = stoi(realvalue(dst));
		//realval = maxval(gettype(dst)) + realval;
		//set_real_value(dst, itos(realval));
	//}

	if(options->cmd_option_bool("generate_uppaal_model"))
		uppaal->binary_instruction(dst, op1, op2, operation);

	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s \e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d \e[32m last_address\e[0m  %d %d \e[32m firstaddress \e[0m %d %d\n",
		debug_content(dst).c_str(), variables_generic[dst].type.c_str(), realvalue(dst).c_str(),
		get_is_propagated_constant(dst),
		get_last_address(op1), get_last_address(dst), get_first_address(op1), get_first_address(dst) );

	//printf("real_and_expr %s %s\n", realvalue(dst).c_str(), eval(content_smt(dst)).c_str() );

}

void SolverWrapper::assign_instruction(string src, string dst, string fn_name ){

	debug && printf("\n\e[32m Assign_instruction %s = %s \e[0m\n",dst.c_str(),src.c_str() );

	if(!check_mangled_name(src)) assert(0 && "Wrong src for assign");
	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for assign");

		bool forcedfree = is_forced_free(src);
		if(forcedfree){

			clear_variable(src);
		}

	assign_instruction_content(src, dst, fn_name);

		if(forcedfree){
			save_first_content(src, dst);

		}


	//bool forcedfree = is_forced_free(src);

	propagate_unary(src, dst, forcedfree);

	if(!assigning_globals && get_name_hint(dst).substr(0,7) == "global_"){
		is_forced_free(dst, true);
	}

	if(get_name_hint(src).substr(0,7) == "global_" && options->cmd_option_bool("globals_always_free")){
		set_content(dst, get_name_hint(src));
		set_content(src, get_name_hint(src));
		insert_variable(src, get_name_hint(src));
		unset_is_propagated_constant(dst);
	}

	//if( variables[dst].type == "" ) assert(0 && "No type in dst");
	string prev_type = variables_generic[dst].type;
	string new_type = get_type(src);

	settype(dst, gettype(src));

	if(is_constant(src) && prev_type != new_type && prev_type != "Pointer" && prev_type != ""){
		printf("Types %s %s\n", prev_type.c_str(), new_type.c_str());
		settype(dst, prev_type);
	}

	if(variables_generic[dst].type == "")
		settype(dst, prev_type);

	//printf("set_real_value inside assign %s %s %s\n", dst.c_str(), src.c_str(), realvalue(src).c_str() );
	set_real_value( dst, realvalue(src) );

	if(options->cmd_option_bool("generate_uppaal_model")){
		if(assigning_globals){
			uppaal->assign_global(src,dst);
		} else {
			uppaal->assign_instruction(src, dst, fn_name );
		}
	}



	//debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s\n", variables[dst].content.c_str(), variables[dst].type.c_str() );
	debug && printf("\e[32m Content_dst \e[0m %s \e[32m type \e[0m %s %s %s\e[32m realvalue \e[0m %s \e[32m propconstant \e[0m %d %d \e[32m lastaddress\e[0m  %d %d \e[32m \e[32m firstaddress \e[0m \e[0m %d %d\n",
                 debug_content(dst).c_str(),
		 variables_generic[src].type.c_str(), variables_generic[dst].type.c_str(), prev_type.c_str(),
		 realvalue(dst).c_str(), get_is_propagated_constant(src), get_is_propagated_constant(dst),
		 get_last_address(src), get_last_address(dst), get_first_address(src), get_first_address(dst) );






	//printf("real_and_expr %s %s\n", realvalue(dst).c_str(), eval(content_smt(dst)).c_str() );





}


int SolverWrapper::minval(string type){

	if (type == "IntegerTyID32" ) return -(1<<30 ) ;
	if (type == "IntegerTyID64" ) return -(1<<30 ) ;
	if (type == "IntegerTyID8"  ) return -128;
	if (type == "IntegerTyID16" ) return -(1<<15 ) ;
	if (type == "Int"           ) return -(1<<30 ) ;
	if (type == "PointerTyID"   ) return 0;
	if (type == "Pointer"       ) return 0;
	if (type == "bool"          ) return 0;


	printf("MinVal unknown type %s\n", type.c_str()); fflush(stdout);
	if(isdriver) assert(0 && "Unknown type");
	return 0;
}

int SolverWrapper::maxval(string type){

	if (type == "IntegerTyID32" ) return (1<<30 ) ;
	if (type == "IntegerTyID64" ) return (1<<30 ) ;
	if (type == "IntegerTyID8"  ) return 127;
	if (type == "IntegerTyID16" ) return (1<<15 ) ;
	if (type == "Int"           ) return (1<<30 ) ;
	if (type == "PointerTyID"   ) return (1<<30);
	if (type == "Pointer"       ) return (1<<30);
	if (type == "bool"          ) return 1;

	printf("MaxVal unknown type %s\n", type.c_str()); fflush(stdout);
	if(isdriver) assert(0 && "Unknown type");
	return 0;

}


void SolverWrapper::set_last_address(string name, int last_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_last_address");

	debug && printf("\e[32m set_last_address %s %d \e[0m\n", name.c_str(), last_address);

	variables_generic[name].last_address = last_address;

}

void SolverWrapper::set_first_address(string name, int first_address){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for set_first_address");

	debug && printf("\e[32m set_first_address %s %d \e[0m\n", name.c_str(), first_address);

	variables_generic[name].first_address = first_address;

}


int SolverWrapper::get_last_address(string name){

	int ret;

	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_last_address");
	if(is_constant(name)) ret = 0;
	else ret = variables_generic[name].last_address;


	if(is_free_var(name)) ret = maxval(gettype(name));

	//assert(ret >= 0    && "Negative last_address");
	//assert(ret <= 1000 && "too-big  last_address");

	// debug && printf("\e[32m get_last_address %s %d \e[0m\n", name.c_str(),ret);

	return ret;

}


int SolverWrapper::get_first_address(string name){

	int ret;
	if(!check_mangled_name(name)) assert(0 && "Wrong name for get_first_address");
	if(is_constant(name)) ret = 0;
	else ret = variables_generic[name].first_address;

	if(is_free_var(name)) ret = minval(gettype(name));

	//assert(ret >= 0    && "Negative first_address");
	//assert(ret <= 1000 && "too-big  first_address");

	// debug && printf("\e[32m get_first_address %s %d \e[0m\n", name.c_str(),ret);

	return ret;

}

void SolverWrapper::set_outofbounds(string varname, bool outofbounds){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for get_outofbounds");

	variables_generic[varname].outofbounds = outofbounds;
}

bool SolverWrapper::get_outofbounds(string varname){

	if(!check_mangled_name(varname)) assert(0 && "Wrong name for get_outofbounds");

	return variables_generic[varname].outofbounds;
}

void SolverWrapper::get_context(SolverWrapper* other){
	variables_generic = other->variables_generic;
	path_stack = other->path_stack;
	conditions_static = other->conditions_static;
}


void SolverWrapper::get_context_back(SolverWrapper* other){
	free_variables = other->free_variables;
	variables_generic = other->variables_generic;
	first_content_value = other->first_content_value;
	path_stack = other->path_stack;
	conditions_static = other->conditions_static;
}

void SolverWrapper::dump_file_initializations(string filename){

	printf("SolverWrapper::dump_file_initializations %s\n", filename.c_str());

	if(options->cmd_option_bool("use_db_for_fi")){

		for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
			string init;
			if(it->value == ""){
				init = variables_generic[it->name].real_value;
			} else {
				init = it->value;
			}
			database->insert_fi(filename, it->position, init);
		}

	} else {
		FILE* file = fopen(tmp_file(filename).c_str(), "w");


		for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
			//fprintf(file, "%s %s\n", it->name.c_str(), variables_generic[it->name].real_value.c_str() );
			string init;
			if(it->value == ""){
				init = variables_generic[it->name].real_value;
			} else {
				init = it->value;
			}
			printf("\e[32m dump_initialization \e[0m %s %s\n", it->position.c_str(), init.c_str() );
			fprintf(file, "%s %s\n", it->position.c_str(), init.c_str() );
		}

		fclose(file);
	}
}

void SolverWrapper::load_file_initializations(){

	printf("SolverWrapper::load_file_initializations\n");


	if(options->cmd_option_bool("use_db_for_fi")){
		initializations = database->load_fi(options->cmd_option_str("file_initializations"));
	} else {
		ifstream input(tmp_file(options->cmd_option_str("file_initializations")).c_str());
		string line;

		while( getline( input, line ) ) {
			string position = tokenize(line, " ")[0];
			string value = tokenize(line, " ")[1];
			initializations[position] = value;

			printf("file_initializations %s %s\n", position.c_str(), value.c_str());
		}
	}
	

}

void SolverWrapper::set_assigning_globals(bool value){
	assigning_globals = value;
}

bool SolverWrapper::has_free_variables(){
	return free_variables.size();
}

bool SolverWrapper::get_freed(string name_mem){
	return variables_generic[name_mem].freed;
}

void SolverWrapper::set_freed(string name_mem, bool value){
	printf("set_freed %s %d\n", name_mem.c_str(), value);
	variables_generic[name_mem].freed = value;
}

//void SolverWrapper::insert_variable_and_type(string var, string type){
//
//	printf("insert_variable_and_type %s %s\n", var.c_str(), type.c_str() );
//	NameAndPosition nandp = {var, var, "0"};
//
//	free_variables.insert(nandp);
//	variables_generic[var].type = type;
//	variables_generic[var].real_value = var;
//	variables_generic[var].name_hint = var;
//
//}


