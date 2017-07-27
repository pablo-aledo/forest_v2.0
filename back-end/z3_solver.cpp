/*
 * =====================================================================================
 * /
 * |     Filename:  solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/31/2014 02:52:31 PM
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

#include "z3_solver.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"
#include "architecture.h"
#include <sys/wait.h>

#define check_mangled_name(A) operators->check_mangled_name(A)
#define UNDERSCORE "_"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3Solver::Z3Solver(){
	
}

Z3Solver::~Z3Solver(){
	
}

bool Z3Solver::get_is_sat(string is_sat){

	if( is_sat == "sat" ) return true;
	else return false;
}

bool Z3Solver::check_representable(){
	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(!it->islinear) return false;
	}
	for( map<string,Z3Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(!it->second.islinear) return false;
	}

	return true;
}

void Z3Solver::solve_problem(){

	//check for max_depth
	if(options->cmd_option_str("max_depth") != "" && conditions.size()-1 > options->cmd_option_int("max_depth")){
		sat = 0;
		return;
	}

	//Start timer
	timer->start_timer();

	vector<string> ret_vector;


	//set sat = 0
	sat = 0;


	// check representable
	printf("\e[31m Check representable \e[0m\n"); fflush(stdout);
	if( !check_representable() ) return;

	//dump problem
	string filename;
	if(options->cmd_option_bool("sequential_problems")){
		int n = database->get_problem_num();
		filename = "z3_" + itos(n) + ".smt2";
	} else {
		filename = "z3_" + itos(rand()) + ".smt2";
	}

	options->read_options();
	get_name(filename);
	dump_problem(filename);
	debug && printf("\e[31m filename solve problem \e[0m %s\n", filename.c_str() );

	// execute solver

	FILE *fp;
	stringstream command;

	command << "z3_timed 60 " << filename;
	command << " > " << tmp_file("z3_output");




	system(command.str().c_str());





	ifstream input(tmp_file("z3_output").c_str());
	string line;
	
	while( getline( input, line ) ) {
		ret_vector.push_back(line);
	}
	
	string         sat_str       = ret_vector[0];

	if(sat_str.find("error") != string::npos ){
		printf("error_in_z3 %s\n", sat_str.c_str());
		if(isdriver) assert(0 && "Error in z3 execution");
	}
	if(sat_str.find("unknown") != string::npos )
		printf("Warning: unknown sat\n");

	// get sat or unsat
	sat = get_is_sat(sat_str);

	debug && printf("\e[31m problem solved \e[0m\n" );


	if(options->cmd_option_bool("rm_z3_queries")){
		system(("rm -f " + filename).c_str());
		system("rm -f z3_output");
	}



	// if unsat then return 
	if(!sat){
		timer->end_timer("solver");
		return;
	}


	bool sat = 0;

	// set values for free_variables (varname, hint and value)

	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	set<NameAndPosition> free_variables_aux;

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;
		if(line.find("error") != string::npos )
			if(isdriver) assert(0 && "Error in z3 execution");

		string varname = it->name;
		string value = canonical_representation(result_get(*it_ret));
		string hint = it->position;


		debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
		//it->value = value;
		//set_real_value_hint(hint, value);
		//variables[varname].real_value = value;

	}

	free_variables = free_variables_aux;

	// set values for variables (name and value)

	for( map<string,Z3Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;
		if(line.find("error") != string::npos )
			if(isdriver) assert(0 && "Error in z3 execution");

		string name = it->first;
		string value = canonical_representation(result_get(*it_ret));


		debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);
		//variables[name].real_value = value;

		it_ret++;
	}

	// set values for first_content

	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, canonical_representation(result_get(*it_ret)));

		it_ret++;
	}

	// end timer
	timer->end_timer("solver");
}

string Z3Solver::result_get(string get_str){


	get_str.erase(get_str.find_last_not_of(" \n\r\t")+1);

	vector<string> tokens = tokenize( get_str, "() ");

	if(tokens.size() < 2){
		printf("%s\n", get_str.c_str() );
		assert(0 && "result_get error");	
	}

	string ret;

	if( tokens[tokens.size() - 2] == "-" )
		ret = "-" + tokens[tokens.size() - 1];
	else 
		ret = tokens[tokens.size() - 1];

	if(ret[ret.length()-1] == '?') ret = ret.substr(0, ret.length()-1);

	if(!is_number(ret)) printf("nan_result %s %s\n", ret.c_str(), get_str.c_str());
	assert( is_number(ret) && "Result is not a number");

	return ret;
}

void Z3Solver::cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext){


	assert(type_src != "" && "Unknown source type");
	assert(type_dst != "" && "Unknown dest   type");


	printf("cast_instruction_types %s %s %s %s\n", type_src.c_str(), type_dst.c_str(), z3_type(type_src).c_str(), z3_type(type_dst).c_str() );

	if(sext == "true")
		setcontent(dst, "(cast_s_" + type_src + "_" + type_dst + " " + content(src) + ")" );
	else
		setcontent(dst, "(cast_z_" + type_src + "_" + type_dst + " " + content(src) + ")" );

	//if( z3_type(type_src) == "Int" && z3_type(type_dst) == "Real" )
		//setcontent(dst, "(to_real " + content(src) + ")" );

	//if( z3_type(type_src) == "Real" && z3_type(type_dst) == "Int" )
		//setcontent(dst, "(to_int " + content(src) + ")" );
	
	//printf("real_and_expr_z3solver %s %s\n", realvalue(dst).c_str(), eval(content_smt(dst)).c_str() );
	//printf("real_and_expr_z3solver %s\n", realvalue(dst).c_str() );
	//printf("real_and_expr_z3solver %s\n", eval(content_smt(dst)).c_str() );

	
}


void Z3Solver::dump_conditions(FILE* file){


	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		fprintf(file,"(assert %s)\n",it->content.c_str() );
	}
	
}

void Z3Solver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void Z3Solver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,Z3Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		//printf("----- name %s type %s\n", it->first.c_str(), gettype(it->first).c_str() );

		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->second.content).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	
	for( map<string,string>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", internal_condition(it->second).c_str(), it->first.c_str());
	}
	
	
	
}

void Z3Solver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}





void Z3Solver::right_shift(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(>> " << content(op1) << " " << content(op2) << ")";


}

void Z3Solver::left_shift(string op1, string op2, string dst, stringstream& content_ss){

	content_ss << "(<< " << content(op1) << " " << content(op2) << ")";




}

void Z3Solver::and_operation(string op1, string op2, string dst, stringstream& content_ss){


	int uniq_num = rand();
		content_ss << "(Y" << bits(gettype(op1)) << "_" << uniq_num << " " << content(op1) << " " << content(op2) << ")";


}

void Z3Solver::or_operation(string op1, string op2, string dst, stringstream& content_ss){


	int uniq_num = rand();
		content_ss << "(O" << bits(gettype(op1)) << "_" << uniq_num << " " << content(op1) << " " << content(op2) << ")";


}


string Z3Solver::z3_type(string type){
	if(type == "Pointer")
		return "Int";
	if(type == "FloatTyID")
		return "Real";
	if(type == "IntegerTyID32")
		return "Int";

	return type;
}


bool Z3Solver::need_for_dump(string name, string content){
		if( content == "" ) return false;
		if( gettype(name) == "Function") return false;
		if( get_is_propagated_constant(name) ) return false;
		return true;
}

void Z3Solver::neq_operation(string op1, string op2, string dst, stringstream& content_ss){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

		content_ss << "(not (= " << content(op1 ) << " " <<  content(op2 ) << "))";

		if(get_type(op1) == "bool" && op2 == "constant_0"){
			content_ss.str("");
			content_ss << "(not (= " << content(op1) << " " << "false" << "))";
		}

		//fflush(stdout); fflush(stderr);
		//printf("realvalue_op1 %s realvalue_op2 %s\n", realvalue(op1).c_str(), realvalue(op2).c_str() );

}

void Z3Solver::rem_operator(string op1, string op2, string dst, stringstream& content_ss){

		content_ss << "(% " << content(op1 ) << " " <<  content(op2 ) << ")";


}




void Z3Solver::leq_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}
	content_ss << "(<= " << content(op1 ) << " " <<  content(op2 ) << ")";
}


void Z3Solver::ugt_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}
	content_ss << "(u> " << content(op1 ) << " " <<  content(op2 ) << ")";

}


void Z3Solver::ugeq_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}
	content_ss << "(u>= " << content(op1 ) << " " <<  content(op2 ) << ")";

}

void Z3Solver::ult_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}
	content_ss << "(u< " << content(op1 ) << " " <<  content(op2 ) << ")";

}



void Z3Solver::uleq_operation(string op1, string op2, string dst, stringstream& content_ss){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}
	content_ss << "(u<= " << content(op1 ) << " " <<  content(op2 ) << ")";

}

void Z3Solver::geq_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}


		content_ss << "(>= " << content(op1 ) << " " <<  content(op2 ) << ")";
}

void Z3Solver::lt_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}


		content_ss << "(< " << content(op1 ) << " " <<  content(op2 ) << ")";
}

void Z3Solver::bt_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}


		content_ss << "(> " << content(op1 ) << " " <<  content(op2 ) << ")";
}

void Z3Solver::eq_operation(string op1, string op2, string dst, stringstream& content_ss){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}


		content_ss << "(= " << content(op1 ) << " " <<  content(op2 ) << ")";
}

void Z3Solver::add_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(+ " << content(op1 ) << " " <<  content(op2 ) << ")";

}


void Z3Solver::xor_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(X " << content(op1 ) << " " <<  content(op2 ) << ")";

}



void Z3Solver::sub_operation(string op1, string op2, string dst, stringstream& content_ss){


		content_ss << "(- " << content(op1 ) << " " <<  content(op2 ) << ")";


}


void Z3Solver::mul_operation(string op1, string op2, string dst, stringstream& content_ss){


	if(is_constant(op1) || get_is_propagated_constant(op1) || is_constant(op2) || get_is_propagated_constant(op2))
		content_ss << "(*c " << content(op1 ) << " " <<  content(op2 ) << ")";
	else
		content_ss << "(* " << content(op1 ) << " " <<  content(op2 ) << ")";

	if( get_type(dst) == "Real" ){
		string content = content_ss.str();
		myReplace(content, "(* ", "(*f ");
		myReplace(content, "(*c ", "(*cf ");

		content_ss.str("");
		content_ss << content;
	}

}

void Z3Solver::div_operation(string op1, string op2, string dst, stringstream& content_ss){

		if(get_type(dst) == "Int" && options->cmd_option_str("solver") == "real_integer"){
			content_ss << "(to_int (/ " << content(op1 ) << " " <<  content(op2 ) << "))";
		} else {
			content_ss << "(/ " << content(op1 ) << " " <<  content(op2 ) << ")";
		}


}


string Z3Solver::internal_representation(int a, string type){
	return itos(a);
}

void Z3Solver::remv_op_constant(string& condition){
	myReplace(condition, "(*c ", "(* ");

}


string Z3Solver::content( string name ){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	if(is_constant(name))
		return name;

	if( variables[name].content == "" || is_forced_free(name) ){
		string position;
	        if(name.substr(0,7) == "global_")
			position = operators->get_actual_function() + UNDERSCORE + variables_generic[name].name_hint;
		else
			position = variables_generic[name].name_hint;
		insert_variable(name, position );

		if(is_number(name)) return name;
		else return position;
		//return name;

	} else {
		if(get_is_propagated_constant(name))
			return "constant_" + gettype(name) + "_" + realvalue(name);
		else
			return variables[name].content;
	}
}




void Z3Solver::assign_instruction_content(string src, string dst, string fn_name){

		variables[dst].content = content(src);


}


void Z3Solver::binary_instruction_content(string dst, string op1, string op2, string operation){


	stringstream content_ss;
	proplinear = true;

	if( operation == "#" ){ // neq_operation
		neq_operation(op1, op2, dst, content_ss);
	} else if (operation == "%") { // rem_operator
		rem_operator(op1, op2, dst, content_ss);
	} else if (operation == "u%") { // rem_operator
		rem_operator(op1, op2, dst, content_ss);
	} else if (operation == "R" ) { // right_shift
		right_shift(op1, op2, dst, content_ss);
	} else if (operation == "L" ) { // left_shift
		left_shift(op1, op2, dst, content_ss);
	} else if (operation == "Y" ) { // and_operation
		and_operation(op1, op2, dst, content_ss);
	} else if (operation == "O" ) { // or_operation
		or_operation(op1, op2, dst, content_ss);
	} else if (operation == "X" ) { // xor_operation
		xor_operation(op1, op2, dst, content_ss);
	} else if(operation == "<="){ // leq_operation
		leq_operation(op1, op2, dst, content_ss);
	} else if(operation == "u>"){ // ugt_operation
		ugt_operation(op1, op2, dst, content_ss);
	} else if(operation == "u>="){ // ugeq_operation
		ugeq_operation(op1, op2, dst, content_ss);
	} else if(operation == "u<"){ // ult_operation
		ult_operation(op1, op2, dst, content_ss);
	} else if(operation == "u<="){ // uleq_operation
		uleq_operation(op1, op2, dst, content_ss);
	} else if(operation == ">="){ // geq_operation
		geq_operation(op1, op2, dst, content_ss);
	} else if(operation == "<"){ // lt_operation
		lt_operation(op1, op2, dst, content_ss);
	} else if(operation == ">"){ // bt_operation
		bt_operation(op1, op2, dst, content_ss);
	} else if(operation == "="){ // eq_operation
		eq_operation(op1, op2, dst, content_ss);
	} else if(operation == "+"){ // add_operation
		add_operation(op1, op2, dst, content_ss);
	} else if(operation == "-"){ // sub_operation
		sub_operation(op1, op2, dst, content_ss);
	} else if(operation == "*"){ // mul_operation
		mul_operation(op1, op2, dst, content_ss);
	} else if(operation == "/"){ // div_operation
		div_operation(op1, op2, dst, content_ss);
	}



	variables[dst].content = content_ss.str();


}


void Z3Solver::setcontent(string varname, string content){


	debug && printf("\e[32m setcontent %s %s\e[0m.\n", varname.c_str(), content.c_str() );

	if(!check_mangled_name(varname)) assert(0 && "Wrong src for setcontent");
	variables[varname].content = content;
}


void Z3Solver::propagate_unary_extra(string src, string dst, bool forcedfree){


	set_offset_tree(dst, get_offset_tree(src));

	variables[dst].idx_values = variables[src].idx_values;
	
	init_indexes(dst, src);

	if(!islinear(src)){
		set_non_linear(dst);
	}

}


void Z3Solver::propagate_binary_extra(string op1, string op2, string dst){


	variables[dst].idx_values = variables[op1].idx_values;
	
	init_indexes(dst, op1, op2);

	if(!islinear(op1) || !islinear(op2) || !proplinear ) 
		set_non_linear(dst);
	else
		variables[dst].islinear = variables[op1].islinear && variables[op2].islinear;

}

void Z3Solver::init_indexes(string dst, string op1, string op2){

	if(!check_mangled_name(dst)) assert(0 && "Wrong name for init_indexes");
	if(!check_mangled_name(op1)) assert(0 && "Wrong name for init_indexes");
	if( op2 != "" && !check_mangled_name(op2)) assert(0 && "Wrong name for init_indexes");

	//printf("variables[%s].indexes.size = %lu\n", op1.c_str(), variables[op1].indexes.size());

	if(is_free_var(op1)){
		variables[dst].indexes.insert(op1);
		debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), op1.c_str());
	}
	set<string> idx_1 = variables[op1].indexes;

	//printf("idx_size %lu\n", idx_1.size());

	for( set<string>::iterator it = idx_1.begin(); it != idx_1.end(); it++ ){
		variables[dst].indexes.insert(*it);
		debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), it->c_str());
	}

	if(op2 != ""){
		if(is_free_var(op2)){
			variables[dst].indexes.insert(op2);
			debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), op2.c_str());
		}

		set<string> idx_2 = variables[op2].indexes;

		for( set<string>::iterator it = idx_2.begin(); it != idx_2.end(); it++ ){
			variables[dst].indexes.insert(*it);
			debug && printf("\e[32m init_indexes \e[0m %s %s\n", dst.c_str(), it->c_str());
		}
	}

	//printf("variables[%s].indexes.size = %lu\n", dst.c_str(), variables[dst].indexes.size());
	
}


string Z3Solver::get_offset_tree( string varname ){

	//assert(check_mangled_name(varname) && "Incorrect name for get_offset_tree");
	//printf("get_offset_tree %s %s\n", varname.c_str(), variables[varname].tree.c_str() );
	return variables[varname].tree;
}


void Z3Solver::set_offset_tree( string varname, string tree ){

	//assert(check_mangled_name(varname) && "Incorrect name for set_offset_tree");
	//printf("set_offset_tree %s %s\n", varname.c_str(), tree.c_str() );
	variables[varname].tree = tree;
}


void Z3Solver::add_range_index(string dst, map<set<pair<string, int> > , int > map_idx_val ){

	if(!check_mangled_name(dst)) assert(0 && "Wrong dst for add_range_index");

	printf("add_range_index %s\n", dst.c_str());

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > idx_vals = it->first;
		int val2 = it->second;
		for( set<pair<string, int> >::iterator it2 = idx_vals.begin(); it2 != idx_vals.end(); it2++ ){
			string idx = it2->first;
			int    val = it2->second;
			printf("idx_vals %s %d %d\n", idx.c_str(), val, val2);
		}
		
	}
	
	variables[dst].idx_values = map_idx_val;

	//pair<int, int> range = pair<int, int>(first_address, last_address);
	//pair<string, pair<int, int> > expr_and_range = pair<string, pair<int, int> >(expr, range);
	//variables[dst].range_indexes.push_back(expr_and_range);

}


void Z3Solver::add_indexes(string dst, vector<string> indexes){
	if(!check_mangled_name(dst)) assert(0 && "wrong name for add_indexes");

	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		variables[dst].indexes.insert(*it);
	}
	

}


void Z3Solver::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){

	if(!check_mangled_name(dst)) assert(0 && "wrong name for pointer_instruction");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(*it)) assert(0 && "wrong name for pointer_instruction");
	}
	


	debug && printf("\e[32m pointer_instruction %lu\e[0m\n", indexes.size() ); fflush(stdout);

	vector<int> jmp_offsets = jump_offsets(offset_tree);


	while(jmp_offsets.size() > indexes.size()){
		jmp_offsets.erase(jmp_offsets.begin());
	}

	assert(jmp_offsets.size() == indexes.size());

	int first_address = get_first_address(base);
	int last_address = get_last_address(base);

	if(last_address-first_address > 1000){
		printf("huge dereference range\n");

			database->insert_outofbounds();
			database->insert_trace();
			printf("Out of Bounds\n");
			exit(0);
	}
	

	string expr = "(+ " + content(base) + " ";
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		stringstream subexpr;
		subexpr << "(* " << content(indexes[i]) << " constant_PointerTyID_" << jmp_offsets[i] << ") ";
		expr += subexpr.str();
	}
	expr += ")";


	int real_pointer = stoi(realvalue(base));
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		// printf("rvii %s %s\n", indexes[i].c_str(), realvalue(indexes[i]).c_str() );
		real_pointer += (stoi(realvalue(indexes[i])) * jmp_offsets[i]);
	}
	// printf("real_pointer %d\n", real_pointer);


	
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		init_indexes(dst, indexes[i]);
	}

	map<set<pair<string, int> > , int > map_idx_val = get_idx_val(base,expr, indexes, first_address, last_address);



	setcontent(dst, expr);
	set_real_value(dst, itos(real_pointer));

	bool forcedfree = is_forced_free(base);
	propagate_unary(base, dst, forcedfree);

	add_range_index(dst, map_idx_val);
	add_indexes(dst, indexes);

	//printf("range_index %d\n", variables[dst].idx_values.size() );
	settype(dst, "Pointer");

	debug && printf("\e[32m pointer_instruction \e[0m  expr %s last_addr %d first_addr %d last_addr %d first_addr %d range_index %lu\n",
			expr.c_str(),
			get_last_address(base), get_first_address(base),
			get_last_address(dst) , get_first_address(dst),
			variables[dst].idx_values.size()
			);

	//exit(0);

}

map<set<pair <string, int> >, int> Z3Solver::get_map_idx_val(string name){
	return variables[name].idx_values;
}

string Z3Solver::get_idx_type(string addr){

	printf("\e[32m get_idx_type %s \e[0m\n", addr.c_str());

	return get_type( "mem_" + itos(variables[addr].idx_values.begin()->second ));

}





void Z3Solver::sym_load(string dst, string addr){

	if(!check_mangled_name(dst)) assert(0 && "Wrong name for sym_load");
	if(!check_mangled_name(addr)) assert(0 && "Wrong name for sym_load");

	string idx_content = content(addr);




	stringstream result_expr;

	map<set<pair<string, int> > , int > map_idx_val = variables[addr].idx_values;

	if( !map_idx_val.size() && variables_generic[addr].last_address - variables_generic[addr].first_address > 1000 ){

		if(!get_free_variables().size() || empty_assertions() ){
			database->insert_outofbounds();
			database->insert_trace();
			printf("Out of Bounds\n");
			exit(0);
		}
		solve_problem();
		if(!solvable_problem())
			exit(0);
		database->insert_outofbounds();
		database->insert_trace();
		printf("Out of Bounds\n");
		exit(0);
	}


	debug && printf("\e[31m sym_load %s %s %lu\e[0m\n", dst.c_str(), addr.c_str(), map_idx_val.size() );


	vector<string> mem_names;

	int m = 0;
	string mem_type;
	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		stringstream and_expr;

		if(elem_idx_val.size() > 1){
			and_expr << "(and ";
		}
		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> elem = (*it2);
			string idx = elem.first;
			string type_idx = gettype("mem_" + realvalue(find_by_name_hint(idx)));
			int idx_val = elem.second;
			
			and_expr << "(= " << idx << " constant_" << type_idx << "_" << idx_val << ")";
		}
		if(elem_idx_val.size() > 1){
			and_expr << ")";
		}

		string mem_val = content("mem_" + itos(val));
		mem_type = gettype("mem_" + itos(val));


		mem_names.push_back("mem_" + itos(val));

		result_expr << "(ite " << and_expr.str() << " " << mem_val << " ";
		m++;
	}
	result_expr << "constant_" << mem_type << "_0";
	for ( unsigned int i = 0; i < m; i++) {
		result_expr << ")";
	}

	setcontent(dst, result_expr.str());

	unset_is_propagated_constant(dst);

	m = 0;
	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> idxv = (*it2);
			printf("symload %s %d %d %s %s\n", idxv.first.c_str(), idxv.second, val,mem_names[m].c_str(), content(mem_names[m]).c_str() );
		}
		m++;
	}





	load_idx_vals(dst, map_idx_val);

	string type = get_idx_type(addr);
	settype(dst, type );


	
	int actual_addr = stoi(realvalue(addr));
	string actual_value = realvalue("mem_" + itos(actual_addr));

	set_real_value(dst, actual_value);

	printf("\e[32m actual_addr \e[0m %d \e[32m actual_value \e[0m %s\n", actual_addr, actual_value.c_str());

	printf("\e[32m Variable_load \e[0m dst %s content %s result_expr %s actual_addr %d actual_value %s\n", dst.c_str(), idx_content.c_str(),result_expr.str().c_str(),
			actual_addr, actual_value.c_str() );

	//exit(0);

}


void Z3Solver::sym_store(string src, string addr){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for sym_store");
	if(!check_mangled_name(addr)) assert(0 && "Wrong name for sym_store");

	string idx_content = content(addr);
	string src_content = content(src);


	map<set<pair<string, int> > , int > map_idx_val = variables[addr].idx_values;

	debug && printf("\e[31m sym_store %s %s %lu\e[0m\n", src.c_str(), addr.c_str(), map_idx_val.size() );


	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){

		stringstream result_expr;

		set<pair<string, int> > elem_idx_val = it->first;
		int val = it->second;

		stringstream and_expr;

		if(elem_idx_val.size() > 1){
			and_expr << "(and ";
		}
		for( set<pair<string, int> >::iterator it2 = elem_idx_val.begin(); it2 != elem_idx_val.end(); it2++ ){
			pair<string, int> elem = (*it2);
			string idx = elem.first;
			string type_idx = gettype("mem_" + realvalue(find_by_name_hint(idx)));
			int idx_val = elem.second;
			
			and_expr << "(= " << idx << " constant_" << type_idx << "_" << idx_val << ")";
		}
		if(elem_idx_val.size() > 1){
			and_expr << ")";
		}

		string mem_name = "mem_" + itos(val);
		string mem_val = content(mem_name);

		result_expr << "(ite " << and_expr.str() << " " << src_content << " " << mem_val << ")";

		debug && printf("\e[32m sym_store \e[0m mem_%d %s\n", val, result_expr.str().c_str() );

		setcontent(mem_name, result_expr.str());

		string type = get_type(src);
		settype(mem_name, type);

		unset_is_propagated_constant(mem_name);

	
	}

	store_idx_vals(src, map_idx_val);

	printf("addr_realvalue %s src_realvalue %s\n", realvalue(addr).c_str(), realvalue(src).c_str());

	set_real_value("mem_" + realvalue(addr), realvalue(src));


	//string type = get_idx_type(addr);
	//settype(dst, type );

	//printf("\e[32m Variable_store \e[0m src %s content %s result_expr %s\n", src.c_str(), idx_content.c_str(),result_expr.str().c_str());


}


void Z3Solver::store_idx_vals(string src, map<set<pair<string, int> > , int > map_idx_val){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for store_idx_vals");

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){

		map<set<pair<string, int> >, int> res;

		set<pair<string, int> > idx_idxvals = it->first;
		int val = it->second;

		set<pair<string, int> > idx_idxval_res;

		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			idx_idxval_res.insert(str_int);
		}

		string memname = "mem_" + itos(val);

		map<set<pair<string, int> > , int > mem_idxvals = variables[src].idx_values;
		if(mem_idxvals.size()){
			for( map<set<pair<string, int> > , int >::iterator it3 = mem_idxvals.begin(); it3 != mem_idxvals.end(); it3++ ){
				set<pair<string, int> > mem_idxvals = it3->first;
				int mem_val = it3->second;
				for( set<pair<string, int> >::iterator it4 = mem_idxvals.begin(); it4 != mem_idxvals.end(); it4++ ){
					pair<string, int> str_int = (*it4);
					idx_idxval_res.insert(str_int);
				}

				res[idx_idxval_res] = val;
			}
		} else {
			res[idx_idxval_res] = stoi(realvalue(src));
		}

		variables[memname].idx_values = res;

		debug && printf("\e[32m store_idx_vals \e[0m %s\n", memname.c_str());
		for( map<set<pair<string, int> > , int >::iterator it = res.begin(); it != res.end(); it++ ){
			set<pair<string, int> > idx_idxvals = it->first;
			set<pair<string, int> > idx_idxval_res;

			int val = it->second;

			for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
				pair<string, int> str_int = (*it2);
				string idx = str_int.first;
				int idxval = str_int.second;

				printf("\e[32m idx_values \e[0m %s %d %d\n", idx.c_str(), idxval, val);
			}
		}

	}
	

}


void Z3Solver::load_idx_vals(string dst, map<set<pair<string, int> > , int > map_idx_val){
	if(!check_mangled_name(dst)) assert(0 && "Wrong name for load_idx_vals");

	map<set<pair<string, int> > , int > res;

	for( map<set<pair<string, int> > , int >::iterator it = map_idx_val.begin(); it != map_idx_val.end(); it++ ){
		set<pair<string, int> > idx_idxvals = it->first;
		set<pair<string, int> > idx_idxval_res;

		int val = it->second;


		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			//string idx = str_int.first;
			//int idxval = str_int.second;

			idx_idxval_res.insert(str_int);

		}

		set<pair<string, int> > idx_idxval_res_copy = idx_idxval_res;

		string memname = "mem_" + itos(val);
		map<set<pair<string, int> > , int > mem_idxvals = variables[memname].idx_values;
		if(mem_idxvals.size()){
			for( map<set<pair<string, int> > , int >::iterator it3 = mem_idxvals.begin(); it3 != mem_idxvals.end(); it3++ ){
				set<pair<string, int> > mem_idxvals = it3->first;
				idx_idxval_res = idx_idxval_res_copy;
				int mem_val = it3->second;
				for( set<pair<string, int> >::iterator it4 = mem_idxvals.begin(); it4 != mem_idxvals.end(); it4++ ){
					pair<string, int> str_int = (*it4);
					idx_idxval_res.insert(str_int);
				}

				res[idx_idxval_res] = mem_val;
			}
		} else {
			res[idx_idxval_res] = stoi(realvalue(memname));
		}
	}

	variables[dst].idx_values = res;

	debug && printf("\e[32m load_idx_vals \e[0m %s\n", dst.c_str());
	for( map<set<pair<string, int> > , int >::iterator it = res.begin(); it != res.end(); it++ ){
		set<pair<string, int> > idx_idxvals = it->first;
		set<pair<string, int> > idx_idxval_res;

		int val = it->second;

		for( set<pair<string, int> >::iterator it2 = idx_idxvals.begin(); it2 != idx_idxvals.end(); it2++ ){
			pair<string, int> str_int = (*it2);
			string idx = str_int.first;
			int idxval = str_int.second;

			printf("\e[32m idx_values \e[0m %s %d %d\n", idx.c_str(), idxval, val);
		}
	}
}

void Z3Solver::bool_to_int8(string src, string dst){
	setcontent(dst, "(ite " + content(src) + " constant_IntegerTyID8_1 constant_IntegerTyID8_0)");

	//printf("content(src) .%s.\n", content(src).substr(0,8).c_str());
	//printf("content(src) .%s.\n", content(src).substr(content(src).size()-27).c_str());
	//printf("content(src) .%s.\n", close_str(content(src).substr(9)).c_str());
	if(content(src).size() > 8+27){
		string prefix = content(src).substr(0,8);
		string suffix = content(src).substr(content(src).size()-27);

		if(prefix == "(not (= " && suffix == " constant_IntegerTyID32_0))"){
			string cntent = (content(src).substr(9) == "(")?close_str(content(src).substr(9)):tokenize(content(src), " ")[2];
			setcontent(dst, "(ite (> " + cntent + " constant_IntegerTyID32_0) constant_IntegerTyID8_1 constant_IntegerTyID8_0)");
		}

	}
}


void Z3Solver::bool_to_int32(string src, string dst){
	setcontent(dst, "(ite " + content(src) + " constant_IntegerTyID32_1 constant_IntegerTyID32_0)");

	//printf("content(src) .%s.\n", content(src).substr(0,8).c_str());
	//printf("content(src) .%s.\n", content(src).substr(content(src).size()-27).c_str());
	//printf("content(src) .%s.\n", close_str(content(src).substr(9)).c_str());
	if(content(src).size() > 8+27){
		string prefix = content(src).substr(0,8);
		string suffix = content(src).substr(content(src).size()-27);

		if(prefix == "(not (= " && suffix == " constant_IntegerTyID32_0))"){
			string cntent = (content(src)[8] == '(')?close_str(content(src).substr(8)):tokenize(content(src), " ")[2];
			setcontent(dst, "(ite (> " + cntent + " constant_IntegerTyID32_0) constant_IntegerTyID32_1 constant_IntegerTyID32_0)");
		}

	}
}



string Z3Solver::debug_content( string name ){
	return variables[name].content;
}

string Z3Solver::content_smt(string name){
	return variables[name].content;
}

void Z3Solver::push_condition_var(string name, bool invert ){



	if(!variables[name].islinear){
		Z3Variable var;
		var.islinear = false;
		conditions.push_back(var);
		return;
	}

	string cond = content(name);
	Z3Variable var;
	var.content = internal_condition(invert?negation(cond):cond);

	string type = variables_generic[name].type;

	if(type == "IntegerTyID32")
		var.content = internal_condition("(not (= " + var.content + " constant_IntegerTyID32_0))");

	//printf("push_condition_var %s %s\n", var.content.c_str(), variables_generic[name].type.c_str() );

	conditions.push_back( var );

}

bool Z3Solver::is_cond_sign(string cond){
	if(cond == "=" )  return true;
	if(cond == "#" )  return true;
	if(cond == "<" )  return true;
	if(cond == ">" )  return true;
	if(cond == "<=")  return true;
	if(cond == ">=")  return true;
	if(cond == "u<" ) return true;
	if(cond == "u>" ) return true;
	if(cond == "u<=") return true;
	if(cond == "u>=") return true;

	return false;
}

void Z3Solver::push_condition_static_var(string name, bool invert){

	string cond = content(name);
	//printf("push_condition_static %s\n", cond.c_str());


	string function = operators->get_actual_function();
	string bb = operators->get_actual_bb();

	if(invert)
		cond = "(not " + cond + ")";

	for ( unsigned int i = 0; i < 10; i++) 
		myReplace(cond, "(not (not ", "");

	myReplace(cond, "(not constant_bool_true)", "constant_bool_false");
	myReplace(cond, "(not constant_bool_false)", "constant_bool_true");

	string cond_op;
	if(cond.substr(0,6) == "(not ("){
		//printf("negate %s %s\n", cond.substr(6,1).c_str(), cond.c_str() );
		cond_op = negateop( tokenize(cond.substr(6), " ")[0] );
	} else {
		cond_op = tokenize(cond.substr(1), " ")[0];
	}

	string condition;

	if(options->cmd_option_bool("recursive"))
		condition = operators->flat_function_stack() + "_" + bb + "." + cond_op;
	else
		condition = function + "_" + bb + "." + cond_op;

	if(cond == "constant_bool_true"){
		condition = "true";
	} else if( cond == "constant_bool_false"){
		condition = "false";
	} else {
		//printf("%s\n", cond_op.c_str());
		assert(is_cond_sign(cond_op) && "Not a condition");
	}




	//printf("condition_static %s %s %s : %s\n", function.c_str(), bb.c_str(), cond.c_str(), condition.c_str());

	conditions_static.push_back( condition );

}

string Z3Solver::negation(string condition){


	stringstream negation_ss;
	negation_ss << "(not " << string(condition) << ")";

	return negation_ss.str();
}


void Z3Solver::variable_store(string src, string idx_content, int first_address, int last_address ){

	if(!check_mangled_name(src)) assert(0 && "Wrong name for variable_store");

	string index_expr = idx_content.substr(5);

	string src_content  = content(src);

	for ( unsigned int i = first_address; i <= last_address; i++) {


		string mem_name = "mem_" + itos(i);
		if(get_name_hint(mem_name) == "") continue;

		string prev_content = content(mem_name);

		stringstream result_expr;
		result_expr << "(ite (= " << index_expr << " " << i << ") " << src_content << " " << prev_content << ")";

		setcontent(mem_name, result_expr.str());
		settype(mem_name, get_type(src));
		unset_is_propagated_constant(mem_name);

	}



	printf("\e[32m Variable_store \e[0m src %s content %s first_addr %d last_addr %d \n",src.c_str(),
			idx_content.c_str(), first_address, last_address);



}

void Z3Solver::set_non_linear(string var){
		variables[var].islinear = false;
		if(variables[var].content.size() == 0) variables[var].content = "!";
		if(variables_generic[var].real_value == "") variables_generic[var].real_value = "0";
		if(variables_generic[var].type == "") variables_generic[var].type = "IntegerTyID32";
}

void Z3Solver::clear_variable(string var){
	variables[var].content = "";
}


void Z3Solver::save_first_content(string var, string dst){
	first_content[var] = variables[dst].content;
}

bool Z3Solver::solvable_problem(){


	return sat;
	
}


void Z3Solver::set_sat(bool _sat){

	spent_time = 0;
	sat = _sat;
}


void Z3Solver::save_state(){
	path_stack_save        = path_stack;
	conditions_static_save = conditions_static;
	conditions_save        = conditions;
}

void Z3Solver::load_state(){
	path_stack        = path_stack_save;
	conditions_static = conditions_static_save;
	conditions        = conditions_save;
}

int Z3Solver::show_problem(){

	printf("\e[33m ==== Constraints: \e[0m\n");
	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("  %s\n", it->content.c_str());
	}
	
	getchar();
}



void Z3Solver::add_eq_zero(string name){

	
	string cond = content(name);
	Z3Variable var;
	var.content = "(= " + cond + " constant_" + gettype(name) + "_0)";
	var.content = internal_condition(var.content);

	printf("\e[32m add_eq_zero \e[0m %s %s\n", name.c_str(), var.content.c_str());


	conditions.push_back( var );

}


void Z3Solver::add_neq_zero(string name){

	string cond = content(name);
	Z3Variable var;
	var.content = "(not (= " + cond + " constant_" + gettype(name) + "_0))";
	var.content = internal_condition(var.content);

	printf("\e[32m add_eq_zero \e[0m %s %s\n", name.c_str(), var.content.c_str());

	conditions.push_back( var );

}

void Z3Solver::add_bt(string name, string value){

	string cond = content(name);
	Z3Variable var;
	var.content = "(> " + cond + " constant_" + gettype(name) + "_" + value + ")";
	var.content = internal_condition(var.content);

	printf("\e[32m add_bt \e[0m %s %s\n", name.c_str(), var.content.c_str());

	conditions.push_back( var );
}


void Z3Solver::add_lt(string name, string value){

	string cond = content(name);
	Z3Variable var;
	var.content = "(< " + cond + " constant_" + gettype(name) + "_" + value + ")";
	var.content = internal_condition(var.content);

	printf("\e[32m add_lt \e[0m %s %s\n", name.c_str(), var.content.c_str());

	conditions.push_back( var );

}

void Z3Solver::dump_conditions(stringstream& sstream){

	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		sstream << it->content;
	}
	

}

string Z3Solver::get_comma_stack_conditions(){

	stringstream ret;

	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->content;
		ret << condition << ",";
	}


	return ret.str();
	

}

string Z3Solver::get_anded_stack_conditions(){

	stringstream ret;

	if(conditions.size() > 1) ret << "(and ";

	for( vector<Z3Variable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		string condition = it->content;
		ret << condition << " ";
	}

	if(conditions.size() > 1) ret << ")";


	return ret.str();
	

}


void Z3Solver::dump_model(){


	vector<string> outputs = options->cmd_option_vector_str("output");

	debug && printf("\e[32m dump_model %lu \e[0m\n", outputs.size() );

	for( vector<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){

		debug && printf("\e[32m dumping_model %s \e[0m\n", it->c_str() );

		string variable = *it;
		string content_var = internal_condition(content(variable));
		//string path_cond = get_anded_stack_conditions();
		string path_cond = get_comma_stack_conditions();
		database->insert_model_entry(variable, content_var, path_cond);
		
	}
	
	
}

void Z3Solver::add_eq_set(set<pair <string, int> > set_idx_val){


	for( set<pair <string, int> >::iterator it = set_idx_val.begin(); it != set_idx_val.end(); it++ ){

		Z3Variable var;
		//var.content = "(= " + it->first + " constant_" + gettype(it->first) + "_" + itos(it->second) + ")";
		var.content = "(= " + it->first + " constant_IntegerTyID32_" + itos(it->second) + ")";
		var.content = internal_condition(var.content);

		//printf("\e[32m add_eq_zero \e[0m %s %s\n", name.c_str(), var.content.c_str());


		conditions.push_back( var );
	}



}





void Z3Solver::set_content(string name, string value){

	variables[name].content = value;

}

pair<int, int> Z3Solver::get_range(string name){

	printf("getrange\n");

	//return pair<int,int>(1,7);

	int defmin;
	int defmax;

	int min = minval(gettype(name))/2;
	int max = maxval(gettype(name))/2;
	int n = 0;

	while( max-min > 1 ){

		if(n == 0){
			n = 1;
		} else {
			FILE* file = fopen(tmp_file("minmax").c_str(), "r");
			fscanf(file, "%d %d", &min, &max);
			fclose(file);
		}

		printf("min_value_iter %d %d %d\n", min, max, max-min);
		//getchar();
		if(int pid = fork()){
			int status; waitpid(pid, &status, 0);
		} else {
			add_lt(name, itos((max+min)/2) );
			solve_problem();
			if(solvable_problem()){
				max = (max+min)/2;
			} else {
				min = (max+min)/2;
			}

			FILE* file = fopen(tmp_file("minmax").c_str(), "w");
			fprintf(file, "%d %d\n", min,max);
			fclose(file);

			exit(0);
		}
	}

	defmin = min;

	min = minval(gettype(name))/2;
	max = maxval(gettype(name))/2;
	n = 0;

	while( max-min > 1 ){

		if(n == 0){
			n = 1;
		} else {
			FILE* file = fopen(tmp_file("minmax").c_str(), "r");
			fscanf(file, "%d %d", &min, &max);
			fclose(file);
		}

		printf("max_value_iter %d %d %d\n", min, max, max-min);
		//getchar();
		if(int pid = fork()){
			int status; waitpid(pid, &status, 0);
		} else {
			add_bt(name, itos((max+min)/2) );
			solve_problem();
			if(solvable_problem()){
				min = (max+min)/2;
			} else {
				max = (max+min)/2;
			}

			FILE* file = fopen(tmp_file("minmax").c_str(), "w");
			fprintf(file, "%d %d\n", min,max);
			fclose(file);

			exit(0);
		}
	}
	defmax = max;

	printf("get_range_output %s %s %d %d\n", name.c_str(), gettype(name).c_str(), defmin, defmax );

	return pair<int,int>(defmin,defmax);

}





bool Z3Solver::empty_assertions(){

	return conditions.size() == 0;

}


void Z3Solver::add_smt(string smt){


	Z3Variable var;
	var.content = smt;

	conditions.push_back(var);

}
