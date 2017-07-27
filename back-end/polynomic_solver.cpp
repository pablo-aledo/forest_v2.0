/*
 * =====================================================================================
 * /
 * |     Filename:  polynomic_solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/30/2014 12:03:53 PM
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

#include "polynomic_solver.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"

#define check_mangled_name(A) operators->check_mangled_name(A)
#define debug false

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

PolynomicSolver::PolynomicSolver(){
	
}

PolynomicSolver::~PolynomicSolver(){
	
}

void PolynomicSolver::bool_to_int8(string src, string dst){

	//PolyVariable variable = variables[src];
	//variables[dst].polarity = variable.polarity;
	variables[dst] = variables[src];
}


void PolynomicSolver::bool_to_int32(string src, string dst){

	//PolyVariable variable = variables[src];
	//variables[dst].polarity = variable.polarity;
	variables[dst] = variables[src];
}


void PolynomicSolver::dump_free_variables(FILE* file){

	assert(free_variables.size() && "Empty free_variables");

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = z3_type(get_type(it->name));

		//dump_variable(position, type, file);
		fprintf(file,"(declare-fun %s () %s)\n", position.c_str(), type.c_str());

		
	}

}

void PolynomicSolver::equalize(PolyVariable& variable){
	if(variable.polarity == ">"){
		set<string> set; set.insert("");
		variable.content[set] -= 0.1;
		variable.polarity = ">=";
	} else if(variable.polarity == "<"){
		set<string> set; set.insert("");
		variable.content[set] += 0.1;
		variable.polarity = "<=";
	} 
}

void PolynomicSolver::dump_constraints(FILE* file){

	for( vector<PolyVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		PolyVariable variable = *it;

		map<set<string>, float> condition = variable.content;
		string polarity = variable.polarity;

		if(isdriver)assert(polarity != "" && "Constraint without polarity");

		//equalize(variable);

		string string_rep = smt2_representation(variable);
		fprintf(file, "(assert %s)\n", string_rep.c_str());

	}
	

}

bool PolynomicSolver::need_for_dump(string name, map<set<string>, float> content){
		if( content.size() == 0 ) return false;
		if( gettype(name) == "Function") return false;
		if( get_is_propagated_constant(name) ) return false;
		return true;
}

vector<PolyVariable> PolynomicSolver::get_tail(vector<PolyVariable> vect){
	vector<PolyVariable>::iterator it = vect.begin(); it++;
	vector<PolyVariable> ret = vector<PolyVariable>(it, vect.end());
	return ret;
}

PolyVariable PolynomicSolver::bigger(PolyVariable variable){
	variable.polarity = ">";
	return variable;
}

PolyVariable PolynomicSolver::smaller(PolyVariable variable){
	variable.polarity = "<";
	return variable;
}


string PolynomicSolver::z3_type(string type){
	if(type == "Pointer")
		return "Int";
	if(type == "FloatTyID")
		return "Real";
	if(type == "IntegerTyID32")
		return "Int";

	return type;
}

void PolynomicSolver::dump_problem(string filename){

	FILE* file = fopen(filename.c_str(), "w");

	dump_header(file);
	dump_free_variables(file);
	dump_type_limits(file);
	dump_constraints(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);
	dump_statistics(file);

	fclose(file);


}


void PolynomicSolver::dump_statistics(FILE* file){
	fprintf(file, "; ASSERTIONS %lu\n", conditions.size() );
	fprintf(file, "; N_VAR %lu\n", free_variables.size() );


	int maxterms = 0;
	float avgterms = 0;
	for( vector<PolyVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->content.size() > maxterms ) maxterms = it->content.size();
		avgterms += (float)(it->content.size());
	}
	avgterms /= (float)(conditions.size());
	fprintf(file, "; N_TERM_MAX %d\n", maxterms );
	fprintf(file, "; N_TERM_AVG %.3f\n", avgterms );


	int max_grade = 0;
	for( vector<PolyVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		map<set<string>, float> content = it->content;
		for( map<set<string>, float>::iterator it2 = content.begin(); it2 != content.end(); it2++ ){
			if(it2->first.size() > max_grade) max_grade = it2->first.size();
		}
	}
	fprintf(file, "; MAX_GRADE %d\n", max_grade );


}

void PolynomicSolver::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}

void PolynomicSolver::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string,PolyVariable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		fprintf(file,"(get-value (%s)); %s\n", smt2_representation(it->second).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	
	for( map<string,PolyVariable>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", smt2_representation(it->second).c_str(), it->first.c_str());
	}
	
	
	
}

void PolynomicSolver::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void PolynomicSolver::dump_type_limits(FILE* file){

	if(options->cmd_option_bool("unconstrained")) return;


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		vector<string> tokens = tokenize(it->name, " ");

		string name = tokens[0];
		string type = gettype(it->name);

		string position = it->position;

		if( get_type(it->name) != "Real" )
			fprintf(file,"(assert (and (>= %s %d) (<= %s %d)))\n", position.c_str(), minval(type), position.c_str(), maxval(type) );
		
	}
}

void PolynomicSolver::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-option :pp-decimal true)\n");
	fprintf(file,"(set-logic AUFNIRA)\n");
}

string PolynomicSolver::result_get(string get_str){


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

	assert( is_number(ret) && "Result is not a number");

	return ret;
}

bool PolynomicSolver::check_linearity(){

	for( vector<PolyVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(!it->islinear) return false;
	}

	for( map<string,PolyVariable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(!it->second.islinear) return false;
	}

	return true;

}

string PolynomicSolver::correct_type(string type, string line){
	if(type.substr(0,7) == "Integer"){
		return tokenize(line, ".")[0];
	}
	return line;
}

void PolynomicSolver::solve_problem(){
	
	//check for max_depth
	if(options->cmd_option_str("max_depth") != "" && conditions.size()-1 > options->cmd_option_int("max_depth")){
		sat = 0;
		return;
	}

	//Start timer
	timer->start_timer();

	//set sat = 0
	sat = 0;

	// check linearity
	printf("\e[31m check_polynomial \e[0m\n");
	if( !check_linearity() ) return;

	//dump problem
	string filename;
	if(options->cmd_option_bool("sequential_problems")){
		int n = database->get_problem_num();
		filename = "z3_poly_" + itos(n) + ".smt2";
	} else {
		filename = "z3_poly_" + itos(rand()) + ".smt2";
	}
	dump_problem(filename);
	
	// execute solver

	vector<string> ret_vector;

	system(("z3_timed 60 " + filename + " > " + tmp_file("z3_output")).c_str());

	ifstream input(tmp_file("z3_output").c_str());
	string line;
	ret_vector.clear();
	while( getline( input, line ) ) {
		ret_vector.push_back(line);
	}


	if(ret_vector[0].find("error") != string::npos){
		printf("error_in_z3\n");
		if(isdriver) assert(0 && "Error in z3 execution" );
	}


	// get sat or unsat
	sat = (ret_vector[0] == "sat");
	

	debug && printf("\e[31m problem solved \e[0m\n");
	
	// if unsat then return 
	if(!sat){
		timer->end_timer("solver");
		return;
	}
	
	// set values for free_variables (varname, hint and value)

	vector<string>::iterator       it_ret = ret_vector.begin(); it_ret++;

	printf("\e[32m get_values \e[0m free_variables %lu variables %lu first_content %lu ret_vector %lu\n", free_variables.size(), variables.size(), first_content.size(), ret_vector.size());

	set<NameAndPosition> free_variables_aux;

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;


				if(line.find("error") != string::npos){
					if(isdriver) assert(0 && "Error in z3 execution" );
				}


		string varname = it->name;
		string value = result_get(*it_ret);
		string hint = it->position;

		printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s \e[32m type \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str(), gettype(varname).c_str() ); fflush(stdout);
		//debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
	}

	free_variables = free_variables_aux;

	// set values for variables (name and value)

	for( map<string,PolyVariable>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;

		string name = it->first;
		string value = correct_type(gettype(name),result_get(line));

		//debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);
		printf("\e[32m name \e[0m %s \e[32m value \e[0m %s \e[32m type \e[0m %s\n", name.c_str(), value.c_str(), gettype(name).c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);

		it_ret++;
	}

	// set values for first_content

	for( map<string,PolyVariable>::iterator it = first_content.begin(); it != first_content.end(); it++ ){

		string line = *it_ret;
		string name = it->first;
		string value = correct_type(gettype(name),result_get(line));

		set_first_content_value(it->first, value);

		it_ret++;
	}

	// end timer
	timer->end_timer("solver");









}

void PolynomicSolver::cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext){

	assign_instruction(src,dst);

	//printf("cast_instruction_types %s %s %s %s\n", type_src.c_str(), type_dst.c_str(), z3_type(type_src).c_str(), z3_type(type_dst).c_str() );

	//setcontent(dst, "(cast_" + type_src + "_" + type_dst + " " + content(src) + ")" );
}

bool PolynomicSolver::is_empty(string name){
	return variables[name].content.size() == 0;
}

#define UNDERSCORE "_"

map<set<string>, float> PolynomicSolver::content(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	map<set<string>, float> ret;
	

	if(is_constant(name)){
		set<string> set; set.insert("1");
		ret[set] = stof(realvalue(name));
		return ret;
	}


	if( is_empty(name) || is_forced_free(name) ){
		string position;
	        if(name.substr(0,7) == "global_")
			position = operators->get_actual_function() + UNDERSCORE + variables_generic[name].name_hint;
		else
			position = variables_generic[name].name_hint;
		insert_variable(name, position );

		if(is_number(name)){
			set<string> set; set.insert("");
			ret[set] = stof(name);
			return ret;
		} else {
			set<string> set; set.insert(position);
			ret[set] = 1;
			return ret;
		}

	} else {

		if(get_is_propagated_constant(name)){
			set<string> set; set.insert("1");
			ret[set] = stof(realvalue(name));
			return ret;
		} else {
			return variables[name].content;
		}
	}
}

void PolynomicSolver::assign_instruction_content(string src, string dst, string fn_name){

	debug && printf("\e[32m assign_instruction \e[0m %s %s %s\n", src.c_str(), dst.c_str(), fn_name.c_str() );

	map<set<string>, float> src_content = content(src);

	variables[dst].content = src_content;
	variables[dst].polarity = variables[src].polarity;

	//debug && printf("\e[32m result \e[0m %f\n", variables[dst].content[""] );
}

void PolynomicSolver::binary_instruction_content(string dst, string op1, string op2, string operation){

	proplinear = true;

	if( operation == "#" ){ // neq_operation
		neq_operation(op1, op2, dst);
	} else if (operation == "%") { // rem_operator
		rem_operator(op1, op2, dst);
	} else if (operation == "R" ) { // right_shift
		right_shift(op1, op2, dst);
	} else if (operation == "L" ) { // left_shift
		left_shift(op1, op2, dst);
	} else if (operation == "Y" ) { // and_operation
		and_operation(op1, op2, dst);
	} else if (operation == "O" ) { // or_operation
		or_operation(op1, op2, dst);
	} else if (operation == "X" ) { // xor_operation
		xor_operation(op1, op2, dst);
	} else if(operation == "<="){ // leq_operation
		leq_operation(op1, op2, dst);
	} else if(operation == "u>"){ // ugt_operation
		ugt_operation(op1, op2, dst);
	} else if(operation == "u>="){ // ugeq_operation
		ugeq_operation(op1, op2, dst);
	} else if(operation == "u<"){ // ult_operation
		ult_operation(op1, op2, dst);
	} else if(operation == "u<="){ // uleq_operation
		uleq_operation(op1, op2, dst);
	} else if(operation == ">="){ // geq_operation
		geq_operation(op1, op2, dst);
	} else if(operation == "<"){ // lt_operation
		lt_operation(op1, op2, dst);
	} else if(operation == ">"){ // bt_operation
		bt_operation(op1, op2, dst);
	} else if(operation == "="){ // eq_operation
		eq_operation(op1, op2, dst);
	} else if(operation == "+"){ // add_operation
		add_operation(op1, op2, dst);
	} else if(operation == "-"){ // sub_operation
		sub_operation(op1, op2, dst);
	} else if(operation == "*"){ // mul_operation
		mul_operation(op1, op2, dst);
	} else if(operation == "/"){ // div_operation
		div_operation(op1, op2, dst);
	}

}

void PolynomicSolver::xor_operation (string op1, string op2, string dst){
	proplinear = false;
}

void PolynomicSolver::rem_operator  (string op1, string op2, string dst){
	proplinear = false;
}

void PolynomicSolver::and_operation (string op1, string op2, string dst){

	proplinear = false;

}

void PolynomicSolver::or_operation  (string op1, string op2, string dst){

	proplinear = false;

}

void PolynomicSolver::left_shift    (string op1, string op2, string dst){

	if(is_constant(op2) || get_is_propagated_constant(op2)){

		int exponent = 1 << stoi(realvalue(op2));

		map<set<string>, float> content_initial = variables[op1].content;
		map<set<string>, float> content_final;

		for( map<set<string>,float>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			set<string> var = it->first;
			float  val = it->second;

			content_final[var] = content_initial[var] * exponent;
		}

		variables[dst].content = content_final;
	} else {
		proplinear = false;
	}


}

void PolynomicSolver::right_shift   (string op1, string op2, string dst){

	if(is_constant(op2) || get_is_propagated_constant(op2)){

		int exponent = 1 << stoi(realvalue(op2));

		map<set<string>, float> content_initial = variables[op1].content;
		map<set<string>, float> content_final;

		for( map<set<string>,float>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			set<string> var = it->first;
			float  val = it->second;

			content_final[var] = content_initial[var] / exponent;
		}

		variables[dst].content = content_final;
	} else {
		proplinear = false;
	}


}

void PolynomicSolver::bt_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">";


}

void PolynomicSolver::geq_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">=";

}

void PolynomicSolver::div_operation (string op1, string op2, string dst){

	if(is_constant(op2)){
		map<set<string>, float> content_initial = variables[op1].content;
		map<set<string>, float> content_final;

		for( map<set<string>,float>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			set<string>var = it->first;
			float  val = it->second;

			content_final[var] = content_initial[var] / stof(realvalue(op2));
		}

		variables[dst].content = content_final;
		
	} else {
		proplinear = false;
	}

}

void PolynomicSolver::leq_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<=";

}

void PolynomicSolver::lt_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<";

}

void PolynomicSolver::neq_operation(string op1, string op2, string dst ){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "#";

	if(variables[op1].polarity != ""){
		//PolyVariable op2_cmp; op2_cmp[""] = 0;
		//if( content_op2 == op2_cmp )
		if(op2 == "constant_IntegerTyID8_0")
			variables[dst].polarity = variables[op1].polarity;
	}

}

void PolynomicSolver::eq_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "=";


}

void PolynomicSolver::sub_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)) return;

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;


}

void PolynomicSolver::add_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)) return;

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] += it->second;
	}
	
	variables[dst].content = content_dst;


}

void PolynomicSolver::ugt_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">";
}

void PolynomicSolver::ugeq_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">=";
}

void PolynomicSolver::ult_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<";
}

void PolynomicSolver::uleq_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<set<string>, float> content_op1 = content(op1);
	map<set<string>, float> content_op2 = content(op2);
	map<set<string>, float> content_dst = content_op1;

	for( map<set<string>,float>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] -= it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<=";
}

set<string> setunion(set<string> set1, set<string> set2){
	set<string> ret;
	for( set<string>::iterator it = set1.begin(); it != set1.end(); it++ ){
		ret.insert(*it);
	}
	for( set<string>::iterator it = set2.begin(); it != set2.end(); it++ ){
		ret.insert(*it);
	}

	return ret;
	
}

void PolynomicSolver::mul_operation(string op1, string op2, string dst){

	if( ( is_constant(op1) || get_is_propagated_constant(op1) ) && !( is_constant(op2) || get_is_propagated_constant(op2) ) )
		mul_operation(op2, op1, dst);

	if(is_constant(op2)){
		map<set<string>, float> content_initial = variables[op1].content;
		map<set<string>, float> content_final;

		for( map<set<string>,float>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			set<string>var = it->first;
			float  val = it->second;

			content_final[var] = content_initial[var] * stof(realvalue(op2));
		}

		variables[dst].content = content_final;
		
	} else {
		map<set<string>, float> content_op1 = variables[op1].content;
		map<set<string>, float> content_op2 = variables[op2].content;
		map<set<string>, float> content_final;

		for( map<set<string>,float>::iterator it = content_op1.begin(); it != content_op1.end(); it++ ){
			for( map<set<string>,float>::iterator it2 = content_op2.begin(); it2 != content_op2.end(); it2++ ){
				set<string> var1 = it->first;
				set<string> var2 = it2->first;
				float float1 = it->second;
				float float2 = it2->second;

				set<string> vars = setunion(var1, var2);
				float coef = float1*float2;

				content_final[vars] += coef;

			}

		}

		variables[dst].content = content_final;
		
	}



}

string PolynomicSolver::internal_condition(string condition){

	return condition;

}

string PolynomicSolver::internal_representation(int in, string type){

	return type;

}

map<set<pair<string, int> > , int > PolynomicSolver::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){


}

string PolynomicSolver::canonical_representation(string in){

	return in;

}


void PolynomicSolver::sym_store(string src, string addr){


	int first_address = get_first_address(addr);
	int last_address = get_last_address(addr);


	printf("sym_store %s %d %d\n", addr.c_str(), get_first_address(addr), get_last_address(addr));


	for ( unsigned int i = first_address; i <= last_address; i++) {
		string dst = "mem_" + itos(i);
		set_non_linear(dst);
	}

}

void PolynomicSolver::sym_load(string dst, string idx_content){

	printf("sym_load %s %s\n", dst.c_str(), idx_content.c_str());

	set_non_linear(dst);
}

void PolynomicSolver::set_offset_tree( string varname, string tree ){}

void PolynomicSolver::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){


	if(!check_mangled_name(dst)) assert(0 && "wrong name for pointer_instruction");
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		if(!check_mangled_name(*it)) assert(0 && "wrong name for pointer_instruction");
	}


	vector<int> jmp_offsets = jump_offsets(offset_tree);

	assert( jmp_offsets.size() == indexes.size() );


	int first_address = get_first_address(base);
	int last_address = get_last_address(base);



	int real_pointer = stoi(realvalue(base));
	for ( unsigned int i = 0; i < indexes.size(); i++) {
		// printf("rvii %s %s\n", indexes[i].c_str(), realvalue(indexes[i]).c_str() );
		real_pointer += (stoi(realvalue(indexes[i])) * jmp_offsets[i]);
	}
	// printf("real_pointer %d\n", real_pointer);
	set_real_value(dst, itos(real_pointer));

	bool forcedfree = is_forced_free(base);
	propagate_unary(base, dst, forcedfree);

	settype(dst, "Pointer");


	set_non_linear(dst);




	debug && printf("\e[32m pointer_instruction \e[0m last_addr %d first_addr %d last_addr %d first_addr %d\n",
			get_last_address(base), get_first_address(base),
			get_last_address(dst) , get_first_address(dst)
			);

}

string PolynomicSolver::smt2_representation(PolyVariable variable){

	map<set<string>, float> content = variable.content;
	string polarity = variable.polarity;

	stringstream ret;

	if(variable.polarity != ""){
		ret << "(" << variable.polarity << " ";
	}

	if(content.size() > 1){
		ret << "(+ ";
		for( map<set<string>,float>::iterator it = content.begin(); it != content.end(); it++ ){

			set<string> coefs = it->first;

			if(coefs.size() > 0)
				ret << "(* ";
			for( set<string>::iterator it2 = coefs.begin(); it2 != coefs.end(); it2++ ){
				ret << *it2 << " ";
			}

			char second[30];
			sprintf(second, "%.3f", it->second);
			ret << string(second) << " ";


			if(coefs.size() > 0)
				ret << ") ";

		}
		ret << ")";

	} else {
			map<set<string>,float>::iterator it = content.begin();
			set<string> coefs = it->first;

			if(coefs.size() > 0)
				ret << "(* ";
			for( set<string>::iterator it2 = coefs.begin(); it2 != coefs.end(); it2++ ){
				ret << *it2 << " ";
			}

			char second[30];
			sprintf(second, "%.3f", it->second);
			ret << string(second) << " ";


			if(coefs.size() > 0)
				ret << ") ";

	}


	if(variable.polarity != ""){
		ret << " 0)";
	}

	string ret_str = ret.str();
	if(variable.polarity == "#"){
		myReplace(ret_str, "#", "=");
		ret_str = "(not " + ret_str + ")";
	}

	return ret_str;
}

string PolynomicSolver::debug_content( string name ){

	return smt2_representation(variables[name]);

	//map<set<string>, float> content = variables[name].content;

	stringstream ret;

	//for( map<set<string>,float>::iterator it = content.begin(); it != content.end(); it++ ){
		//ret <<  (it==content.begin()?"":"+") << it->second << "·" << it->first ;
	//}

	//if( variables[name].polarity != "" )
		//ret << " " << variables[name].polarity << " 0";
	
	return ret.str();


}

string PolynomicSolver::content_smt(string name){ return ""; }

string PolynomicSolver::negateop_linear(string predicate){

	if( predicate == "="  ) return "#"; 
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	printf("predicate %s\n", predicate.c_str());
	if(isdriver)assert(0 && "Unknown Operation");
}

PolyVariable PolynomicSolver::negate_var(PolyVariable variable){

	if(variable.polarity == ">"){
		set<string> set; set.insert("");
		variable.content[set] -= 1.0;
	}

	variable.polarity = negateop_linear(variable.polarity);


	return variable;

}

void PolynomicSolver::push_condition_var(string name, bool invert  ){
	printf("push_condition_var name %s invert %d\n", name.c_str(), invert);

	if(!variables[name].islinear){
		PolyVariable lv;
		lv.islinear = false;
		conditions.push_back(lv);
		return;
	}

	if(invert){
		PolyVariable variable = negate_var(variables[name]);
		conditions.push_back( variable );
	} else {
		conditions.push_back( variables[name] );
	}

}

void PolynomicSolver::push_condition_static_var(string name, bool invert){


	string function = operators->get_actual_function();
	string bb = operators->get_actual_bb();
	string cond = variables[name].polarity;

	if(invert)
		cond = negateop_linear(cond);


	string condition = function + "_" + bb + "." + cond;


	printf("condition_static %s %s %s : %s\n", function.c_str(), bb.c_str(), cond.c_str(), condition.c_str());

	conditions_static.push_back( condition );
}

void PolynomicSolver::variable_store(string src, string idx_content, int first_address, int last_address ){;}


void PolynomicSolver::set_non_linear(string var){
		variables[var].islinear = false;
		if(variables[var].content.size() == 0){ set<string> set; set.insert("!"); variables[var].content[set] = 0; }
		if(variables_generic[var].real_value == "") variables_generic[var].real_value = "0";
		if(variables_generic[var].type == "") variables_generic[var].type = "IntegerTyID32";
}


void PolynomicSolver::propagate_binary_extra(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2) || !proplinear ) 
		set_non_linear(dst);
	else
		variables[dst].islinear = variables[op1].islinear && variables[op2].islinear;

}

bool PolynomicSolver::islinear(string varname){
	return variables[varname].islinear || is_constant(varname) || get_is_propagated_constant(varname);

}

void PolynomicSolver::propagate_unary_extra(string src, string dst, bool forcedfree){

	if(!islinear(src)){
		set_non_linear(dst);
	}
}

void PolynomicSolver::clear_variable(string var){
	variables[var].content.clear();
}

void PolynomicSolver::save_first_content(string var, string dst){

	first_content[var] = variables[dst];
}

bool PolynomicSolver::solvable_problem(){
	return sat;
}

void PolynomicSolver::set_sat(bool _sat){

	spent_time = 0;
	sat = _sat;

}


void PolynomicSolver::save_state(){
	path_stack_save        = path_stack;
	conditions_static_save = conditions_static;
	conditions_save        = conditions;
}

void PolynomicSolver::load_state(){
	path_stack        = path_stack_save;
	conditions_static = conditions_static_save;
	conditions        = conditions_save;
}

int PolynomicSolver::show_problem(){

	printf("\e[33m ==== Constraints: \e[0m\n");
	for( vector<PolyVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("  %s\n", smt2_representation(*it).c_str());
	}

	getchar();
}





void PolynomicSolver::add_eq_zero(string variable){

	
	PolyVariable var = variables[variable];
	var.polarity = "=";

	printf("\e[32m add_eq_zero \e[0m %s %s\n", variable.c_str(), smt2_representation(var).c_str());


	conditions.push_back( var );

}


void PolynomicSolver::add_neq_zero(string variable){

	
	PolyVariable var = variables[variable];
	var.polarity = "#";

	printf("\e[32m add_neq_zero \e[0m %s %s\n", variable.c_str(), smt2_representation(var).c_str());


	conditions.push_back( var );

}


void PolynomicSolver::dump_conditions(stringstream& sstream){

		assert(0 && "Not Implemented");

}


void PolynomicSolver::dump_model(){

	assert(0 && "Not implemented");

}


map<set<pair <string, int> >, int> PolynomicSolver::get_map_idx_val(string name){
	assert(0 && "Not Implemented");
}

void PolynomicSolver::add_eq_set(set<pair <string, int> > set_idx_val){
	assert(0 && "Not Implemented");
}





void PolynomicSolver::set_content(string name, string value){

	assert(0 && "not implemented");

}

string PolynomicSolver::eval(string expression){
	assert(0 && "Not Implemented");
}


void PolynomicSolver::add_bt(string var, string val){

	assert(0 && "Not Implemented");

}

void PolynomicSolver::add_lt(string var, string val){

	assert(0 && "Not Implemented");

}


pair<int, int> PolynomicSolver::get_range(string name){

	assert(0 && "Not Implemented");

}


bool PolynomicSolver::empty_assertions(){

	assert(0 && "Not Implemented");

}


void PolynomicSolver::add_smt(string smt){

	assert(0 && "Not Implemented");

}
