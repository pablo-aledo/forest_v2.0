/*
 * =====================================================================================
 * /
 * |     Filename:  linear_bblast.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/11/2014 02:24:43 AM
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

#include "linear_bblast.h"
#include "operators.h"
#include "options.h"
#include "timer.h"
#include "database.h"
#include "architecture.h"


extern Operators* operators;
extern Options* options;
extern Timer* timer;
extern Database* database;


LinearBblast::LinearBblast(){

}


LinearBblast::~LinearBblast(){

}


void LinearBblast::bool_to_int8(string src, string dst){

	variables[dst] = variables[src];
}


void LinearBblast::bool_to_int32(string src, string dst){

	variables[dst] = variables[src];
}

void LinearBblast::load_state(){
	path_stack        = path_stack_save;
	conditions_static = conditions_static_save;
	conditions        = conditions_save;
}

void LinearBblast::save_state(){
	path_stack_save        = path_stack;
	conditions_static_save = conditions_static;
	conditions_save        = conditions;
}

void LinearBblast::assign_instruction_content(string src, string dst, string fn_name){

	if(variables[dst].type_rep == ""){
		variables[dst].type_rep = gettype(src);
	}

	if(!islinear(src)){ set_non_linear(dst); return; }

	debug && printf("\e[32m assign_instruction \e[0m %s %s %s\n", src.c_str(), dst.c_str(), fn_name.c_str() );


	map<string, HexNum> src_content = content(src);

	variables[dst].content = src_content;
	variables[dst].polarity = variables[src].polarity;

	//if(gettype(src) != "bool")
	if(variables[src].polarity == "")
		variables[dst].type_rep = gettype(src);
	else 
		variables[dst].type_rep = variables[src].type_rep;

	assert(variables[dst].type_rep != "" && "Assigning empty type_rep");

	//debug && printf("\e[32m result \e[0m %f\n", variables[dst].content[""] );
}



void LinearBblast::binary_instruction_content(string dst, string op1, string op2, string operation){


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
void LinearBblast::cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext){

	assign_instruction(src,dst);
	variables[dst].type_rep = type_dst;

}
string LinearBblast::internal_condition(string condition){

	return condition;

}
string LinearBblast::internal_representation(int in, string type){

	return type;

}

map<set<pair<string, int> > , int > LinearBblast::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

	map<set<pair<string, int> > , int > ret;
	return ret;

}
string LinearBblast::canonical_representation(string in){

	//printf("canonical_representation in %s\n", in.c_str() ); fflush(stdout);
	if(in[0] != '#' && in != "true" && in != "false" && in.find(".") == string::npos )
		assert(0 && "Canonical_Representation of a non-internal");


	if(in == "false") return "false";
	if(in == "true") return "true";

	int a;
	char ret_str[10];
	sscanf(in.substr(2).c_str(), "%x", &a);


	//if(in[2] == '8' || in[2] == '9' || in[2] == 'a' || in[2] == 'b' || in[2] == 'c' || in[2] == 'd' || in[2] == 'e' || in[2] == 'f')
		//sprintf(ret_str, "%d", a - (1<<((in.length()-2)*4)) );
	//else 
		sprintf(ret_str, "%d", a);

	//printf("canonical_representation in %s a %d ret %s\n", in.c_str(), a, ret_str );

	return string(ret_str);

}



void LinearBblast::sym_store(string src, string addr){


	int first_address = get_first_address(addr);
	int last_address = get_last_address(addr);


	printf("sym_store %s %d %d\n", addr.c_str(), get_first_address(addr), get_last_address(addr));


	for ( unsigned int i = first_address; i <= last_address; i++) {
		string dst = "mem_" + itos(i);
		set_non_linear(dst);
	}

}
void LinearBblast::sym_load(string dst, string idx_content){

	printf("sym_load %s %s\n", dst.c_str(), idx_content.c_str());

	set_non_linear(dst);
}
void LinearBblast::set_offset_tree( string varname, string tree ){}



#define check_mangled_name(A) operators->check_mangled_name(A)

void LinearBblast::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){


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



string LinearBblast::content_smt(string name){ return ""; }




void LinearBblast::push_condition_var(string name, bool invert  ){
	printf("push_condition_var name %s invert %d\n", name.c_str(), invert);

	if(!variables[name].islinear){
		LinearVarBb lv;
		lv.islinear = false;
		conditions.push_back(lv);
		return;
	}

	if(invert){
		LinearVarBb variable = negate_var(variables[name]);
		conditions.push_back( variable );
	} else {
		conditions.push_back( variables[name] );
	}

}

LinearVarBb LinearBblast::negate_var(LinearVarBb variable){

	if(variable.polarity == ">"){
		//variable.content[""] -= 1.0;
	}

	variable.polarity = negateop_linear(variable.polarity);


	return variable;

}


string LinearBblast::negateop_linear(string predicate){

	if( predicate == "="  ) return "#"; 
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	printf("predicate %s\n", predicate.c_str());
	if(isdriver)assert(0 && "Unknown Operation");
}



bool LinearBblast::need_for_dump(string name, map<string, HexNum> content){
		if( content.size() == 0 ) return false;
		if( gettype(name) == "Function") return false;
		if( get_is_propagated_constant(name) ) return false;
		return true;
}



void LinearBblast::dump_problem(string filename){



		FILE* file = fopen( filename.c_str(), "w");



		dump_header(file);
		dump_free_variables(file);
		dump_aux_variables(file);
		dump_constraints(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		dump_statistics(file);

		fclose(file);



}



void LinearBblast::dump_constraints(FILE* file){

	int n = 1;
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		LinearVarBb variable = *it;

		map<string, HexNum> condition = variable.content;
		string polarity = variable.polarity;

		if(isdriver)assert(polarity != "" && "Constraint without polarity");

		//equalize(variable);

		string string_rep = smt2_representation(variable);
		fprintf(file, "(assert %s)\n", string_rep.c_str());

	}
	

}

string LinearBblast::adapt_width(string name, string type_free_var, string type_dst){

	//printf("adapt_width %s %s %s\n", name.c_str(), type_free_var.c_str(), type_dst.c_str());
	
	int diff_bits = bits(type_dst) - bits(type_free_var);

	if(diff_bits == 0){
		return name;
	}

	if(diff_bits > 0){
		return "(concat " + concat_begin(diff_bits, 0) + " " + name + ")";
	}

	if( diff_bits < 0 ){
		return "((_ extract " + itos(bits(type_dst)-1) + " 0) " + name + ")";
	}

}

string LinearBblast::bv_polarity(string polarity){

	if(polarity == "=") return "=";
	if(polarity == "<") return "bvslt";
	if(polarity == ">") return "bvsgt";
	if(polarity == "<=") return "bvsle";
	if(polarity == ">=") return "bvsge";
	if(polarity == "u<") return "bvslt";
	if(polarity == "u>") return "bvsgt";
	if(polarity == "u<=") return "bvsle";
	if(polarity == "u>=") return "bvsge";
	if(polarity == "#") return "#";

	printf("%s\n", polarity.c_str());
	assert(0 && "Unknown polarity");

}

string LinearBblast::smt2_representation(LinearVarBb variable){

	map<string,HexNum> content = variable.content;
	string polarity = variable.polarity;

	stringstream ret;

	if(variable.polarity != ""){
		ret << "(" << bv_polarity(variable.polarity) << " ";
	}

	if(content.size() > 1){
		ret << "(bvadd ";
		for( map<string,HexNum>::iterator it = content.begin(); it != content.end(); it++ ){

			char second[30];
			sprintf(second, "%s", it->second.c_str(variable.type_rep));

			if(it->first == ""){
				ret << second << " ";
			} else {
				if(it->second == HexNum(1)){
					ret << adapt_width(it->first, type_free_var(it->first),variable.type_rep) << " ";
				} else {
					ret << "(bvmul " << adapt_width(it->first, type_free_var(it->first),variable.type_rep) << " " << second << ") " ;
				}
			}
		}
		ret << ")";

	} else {
		map<string,HexNum>::iterator it = content.begin();
		char second[30];
		sprintf(second, "%s", it->second.c_str(variable.type_rep));
		if(it->first == ""){
			ret << second << " ";
		} else {
			if(it->second == HexNum(1)){
				ret << adapt_width(it->first, type_free_var(it->first),variable.type_rep) << " ";
			} else {
				ret << "(bvmul " << adapt_width(it->first, type_free_var(it->first),variable.type_rep) << " " << second << ") " ;
			}
		}

	}


	if(variable.polarity != ""){
		ret << " " << HexNum(0).c_str(variable.type_rep) << ")";
	}

	string ret_str = ret.str();
	if(variable.polarity == "#"){
		myReplace(ret_str, "(#", "(=");
		ret_str = "(not " + ret_str + ")";
	}



	return ret_str;
}


string LinearBblast::type_free_var(string name_hint){

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);

		if(position == name_hint){
			return type;
		}
	}

	for( vector<AuxVar>::iterator it = aux_vars.begin(); it != aux_vars.end(); it++ ){
		string name = it->name;
		string type = it->type;


		if( name == name_hint ){
			return type;
		}
	}
	

	printf("name_hint %s\n", name_hint.c_str());
	assert(0 && "Variable not found");

}

void LinearBblast::dump_free_variables(FILE* file){

	assert(free_variables.size() && "Empty free_variables");

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);
		int bits;

		//printf("dump_variables_type %s\n", type.c_str());

		if(type == "IntegerTyID32") {
			bits = 32;
			fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);
		} else if(type == "IntegerTyID64") {
			bits = 64;
			fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);
		} else if(type == "IntegerTyID16") {
			bits = 16;
			fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);
		} else if(type == "IntegerTyID8") {
			bits = 8;
			fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);
		} else if(type == "FloatTyID") {
			fprintf(file,"(declare-const %s (_ FP 11 53))\n", position.c_str());
		} else {
			if(isdriver) assert(0 && "Unknown Type");
		}

	}
	


}

void LinearBblast::dump_aux_variables(FILE* file){
	for( vector<AuxVar>::iterator it = aux_vars.begin(); it != aux_vars.end(); it++ ){
		
		string name = it->name;
		string type = it->type;
		int bits = get_n_bits(type);

		fprintf(file,"(declare-const %s (_ BitVec %d))\n", name.c_str(), bits);
	}
	
}

bool LinearBblast::is_empty(string name){
	return variables[name].content.size() == 0;
}

#define UNDERSCORE "_"

map<string, HexNum> LinearBblast::content(string name){

	if(!check_mangled_name(name)) assert(0 && "Wrong name for content");

	map<string, HexNum> ret;
	

	if(is_constant(name)){
		ret[""] = stof(realvalue(name));
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
			ret[""] = stof(name);
			return ret;
		} else {
			ret[position] = 1;
			return ret;
		}

	} else {

		if(get_is_propagated_constant(name)){
			ret[""] = stof(realvalue(name));
			return ret;
		} else {
			return variables[name].content;
		}
	}
}


void LinearBblast::neq_operation(string op1, string op2, string dst ){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string, HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "#";

	if(variables[op1].polarity != ""){
		//LinearVariable op2_cmp; op2_cmp[""] = 0;
		//if( content_op2 == op2_cmp )
		if(op2 == "constant_IntegerTyID8_0")
			variables[dst].polarity = variables[op1].polarity;
	}

	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));

}



void LinearBblast::rem_operator  (string op1, string op2, string dst){
	proplinear = false;
}



void LinearBblast::right_shift   (string op1, string op2, string dst){


	string uniq_num = itos(rand());

	if(is_constant(op2) || get_is_propagated_constant(op2)){
		int exponent = 1 << stoi(realvalue(op2));


		map<string, HexNum> content_initial = variables[op1].content;
		map<string, HexNum> content_final;

		content_final["new_var" + uniq_num] = HexNum(exponent);
		for( map<string,HexNum>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			content_final[it->first] = HexNum(0) - content_initial[it->first];
		}
		

		LinearVarBb new_restr;
		new_restr.content = content_final;
		new_restr.polarity = "=";
		new_restr.type_rep = variables[op1].type_rep;
		conditions.push_back(new_restr);

		AuxVar aux_var = {"new_var" + uniq_num, gettype(op1)};
		aux_vars.push_back(aux_var);
		

		variables[dst].content.clear();
		variables[dst].content["new_var" + uniq_num] = HexNum(1);
		variables[dst].type_rep = "IntegerTyID32";

		printf("variables[dst] %s\n", smt2_representation(variables[dst]).c_str() );

	} else {
		proplinear = false;
	}


}



void LinearBblast::left_shift    (string op1, string op2, string dst){

	if(variables[op1].content.size() == 0){
		variables[op1].content = content(op1);
		variables[op1].type_rep = gettype(op1);
	}

	if(is_constant(op2) || get_is_propagated_constant(op2)){
		int exponent = 1 << stoi(realvalue(op2));

		map<string, HexNum> content_initial = variables[op1].content;
		map<string, HexNum> content_final;

		for( map<string,HexNum>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			string var = it->first;
			HexNum val = it->second;

			content_final[var] = content_initial[var] * exponent;
		}

		variables[dst].content = content_final;
	} else {
		proplinear = false;
	}



}



void LinearBblast::and_operation (string op1, string op2, string dst){

	proplinear = false;


}



void LinearBblast::or_operation  (string op1, string op2, string dst){

	proplinear = false;

}



void LinearBblast::xor_operation (string op1, string op2, string dst){
	if( !(is_constant(op2) || get_is_propagated_constant(op2)) ){
		proplinear = false;
		return;
	}

	if( realvalue(op2) == "-1" ){
		map<string,HexNum> content_op1 = content(op1);

		for( map<string,HexNum>::iterator it = content_op1.begin(); it != content_op1.end(); it++ ){
			it->second = HexNum(0)-(it->second);
		}

		content_op1[""] = content_op1[""] - HexNum(1);

		variables[dst].content = content_op1;

		
	} else{
		proplinear = false;
	}
}



void LinearBblast::leq_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<=";

	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));
}



void LinearBblast::ugt_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string, HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "u>";
}

void LinearBblast::ugeq_operation(string op1, string op2, string dst){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string, HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "u>=";

}

void LinearBblast::ult_operation(string op1, string op2, string dst){
	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string, HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "u<";

}

void LinearBblast::uleq_operation(string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "u<=";
}



void LinearBblast::geq_operation (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">=";
	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));

}



void LinearBblast::lt_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "<";
	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));

}



void LinearBblast::bt_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = ">";
	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));

}



void LinearBblast::eq_operation  (string op1, string op2, string dst){

	if(!islinear(op1) || !islinear(op2)){set_real_value(dst, "false"); return;}

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;
	variables[dst].polarity = "=";
	variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));


}



void LinearBblast::add_operation (string op1, string op2, string dst){

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] + it->second;
	}
	
	variables[dst].content = content_dst;


}



void LinearBblast::sub_operation (string op1, string op2, string dst){

	map<string, HexNum> content_op1 = content(op1);
	map<string, HexNum> content_op2 = content(op2);
	map<string, HexNum> content_dst = content_op1;

	for( map<string,HexNum>::iterator it = content_op2.begin(); it != content_op2.end(); it++ ){
		content_dst[it->first] = content_dst[it->first] - it->second;
	}
	
	variables[dst].content = content_dst;


}



void LinearBblast::mul_operation(string op1, string op2, string dst){

	if( ( is_constant(op1) || get_is_propagated_constant(op1) ) && !( is_constant(op2) || get_is_propagated_constant(op2) ) )
		mul_operation(op2, op1, dst);

	if(is_constant(op2)){
		map<string, HexNum> content_initial = variables[op1].content;
		map<string, HexNum> content_final;

		for( map<string,HexNum>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			string var = it->first;
			HexNum val = it->second;

			content_final[var] = content_initial[var] * stoi(realvalue(op2));
		}

		variables[dst].content = content_final;
		
	} else {
		proplinear = false;
	}



}



void LinearBblast::div_operation (string op1, string op2, string dst){

	if(is_constant(op2)){
		map<string, HexNum> content_initial = variables[op1].content;
		map<string, HexNum> content_final;

		for( map<string,HexNum>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			string var = it->first;
			HexNum val = it->second;

			content_final[var] = content_initial[var] / stoi(realvalue(op2));
		}

		variables[dst].content = content_final;
		
	} else {
		proplinear = false;
	}

}

void LinearBblast::set_non_linear(string var){
		variables[var].islinear = false;
		variables[var].type_rep = "IntegerTyID8";
		if(variables[var].content.size() == 0) variables[var].content["!"] = 0;
		if(variables_generic[var].real_value == "") variables_generic[var].real_value = "0";
		if(variables_generic[var].type == "") variables_generic[var].type = "IntegerTyID32";
}



void LinearBblast::dump_check_sat(FILE* file){


	fprintf(file,"(check-sat)\n");

}

void LinearBblast::dump_get(FILE* file){



	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file,"(get-value (%s)); %s\n",internal_condition(it->position).c_str(), it->name.c_str() );
	}
	
	fprintf(file,"; --- ↑free ↓non-free \n" );

	for( map<string, LinearVarBb>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;
		
		fprintf(file,"(get-value (%s)); %s\n", smt2_representation(it->second).c_str(), it->first.c_str() );
	}

	fprintf(file,"; --- ↑non-free ↓forced_free \n" );

	
	for( map<string,LinearVarBb>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		fprintf(file, "(get-value (%s)); %s\n", smt2_representation(it->second).c_str(), it->first.c_str());
	}
	
	
	
}

void LinearBblast::dump_tail(FILE* file){

	fprintf(file,"(exit)\n");
}

void LinearBblast::dump_statistics(FILE* file){
	fprintf(file, "; ASSERTIONS %lu\n", conditions.size() );

	int zeros = 0;
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		for( set<NameAndPosition>::iterator it2 = free_variables.begin(); it2 != free_variables.end(); it2++ ){
			//printf("finding %s in %s\n", it2->position.c_str(), smt2_representation(*it).c_str() );
			if( it->content.find(it2->position) == it->content.end() )
				zeros++;
		}
	}
	fprintf(file, "; ZEROS %d\n", zeros );

	float bits = 0;
	int maxbits = -1;
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		bits += get_n_bits(gettype(it->name));
		if( get_n_bits(gettype(it->name)) > maxbits)
			maxbits = get_n_bits(gettype(it->name));
	}
	bits /= (float)(free_variables.size());
	fprintf(file, "; AVG_BITS %.3f\n", bits);
	fprintf(file, "; MAX_BITS %d\n", maxbits);







	int maxterms = 0;
	float avgterms = 0;
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->content.size() > maxterms ) maxterms = it->content.size();
		avgterms += (float)(it->content.size());
	}
	avgterms /= (float)(conditions.size());


	fprintf(file, "; N_TERM_MAX %d\n", maxterms );
	fprintf(file, "; N_TERM_AVG %.3f\n", avgterms );








}


void LinearBblast::solve_problem(){
	
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
	printf("\e[31m Check linearity \e[0m\n"); fflush(stdout);
	if( !check_linearity() ) return;

	//dump problem
	string filename;
	if(options->cmd_option_bool("sequential_problems")){
		int n = database->get_problem_num();
		filename = "z3_linearbblast_" + itos(n) + ".smt2";
	} else {
		filename = "z3_linearbblast_" + itos(rand()) + ".smt2";
	}
	get_name(filename);
	dump_problem(filename);
	printf("\e[31m filename solve problem \e[0m %s\n", filename.c_str() );
	
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

	//printf("\e[32m get_values \e[0m free_variables %d variables %d first_content %d ret_vector %d\n", free_variables.size(), variables.size(), first_content.size(), ret_vector.size());

	set<NameAndPosition> free_variables_aux;

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++,it_ret++ ){

		string line = *it_ret;


				if(line.find("error") != string::npos){
					if(isdriver) assert(0 && "Error in z3 execution" );
				}


		string varname = it->name;
		string value = canonical_representation(result_get(*it_ret));
		string hint = it->position;

		printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);
		//debug && printf("\e[32m name \e[0m %s \e[32m hint \e[0m %s \e[32m value \e[0m %s\n", varname.c_str(), hint.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(varname, value);

		NameAndPosition nandp = {varname, hint, value};
		free_variables_aux.insert(nandp);
	}

	free_variables = free_variables_aux;

	// set values for variables (name and value)

	for( map<string,LinearVarBb>::iterator it = variables.begin(); it != variables.end(); it++ ){

		if(!need_for_dump(it->first, it->second.content)) continue;

		string line = *it_ret;

		string name = it->first;
		string value = canonical_representation(result_get(*it_ret));

		//debug && printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);
		printf("\e[32m name \e[0m %s \e[32m value \e[0m %s\n", name.c_str(), value.c_str() ); fflush(stdout);

		set_real_value_mangled(name, value);

		it_ret++;
	}

	// set values for first_content

	for( map<string,LinearVarBb>::iterator it = first_content.begin(); it != first_content.end(); it++ ){
		set_first_content_value(it->first, canonical_representation(result_get(*it_ret)));

		it_ret++;
	}

	// end timer
	timer->end_timer("solver");









}

void LinearBblast::get_name(string& filename){

}

bool LinearBblast::check_linearity(){

	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if(!it->islinear){
			printf("\e[31m non-linear \e[0m\n");
			return false;
		}
	}

	for( map<string,LinearVarBb>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(!it->second.islinear){
			printf("\e[31m non-linear \e[0m\n");
			return false;
		}
	}

	printf("\e[32m linear \e[0m\n");
	return true;

}


string LinearBblast::result_get(string get_str){


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


void LinearBblast::clear_variable(string var){
	variables[var].content.clear();
}


void LinearBblast::save_first_content(string var, string dst){

	first_content[var] = variables[dst];
}

void LinearBblast::push_condition_static_var(string name, bool invert){


	string function = operators->get_actual_function();
	string bb = operators->get_actual_bb();
	string cond = variables[name].polarity;

	if(invert)
		cond = negateop_linear(cond);


	string condition = function + "_" + bb + "." + cond;


	printf("condition_static %s %s %s : %s\n", function.c_str(), bb.c_str(), cond.c_str(), condition.c_str());

	conditions_static.push_back( condition );
}

void LinearBblast::variable_store(string src, string idx_content, int first_address, int last_address ){;}

string LinearBblast::debug_content( string name ){

	map<string, HexNum> content = variables[name].content;
	string type = variables[name].type_rep;

	assert(type != "" && "Empty type_rep");

	stringstream ret;

	for( map<string,HexNum>::iterator it = content.begin(); it != content.end(); it++ ){
		ret <<  (it==content.begin()?"":"+") << string(it->second.c_str(type)) << "·" << it->first.c_str();
	}

	if( variables[name].polarity != "" )
		ret << " " << variables[name].polarity << " 0";
	
	return ret.str();


}

void LinearBblast::set_sat(bool _sat){

	spent_time = 0;
	sat = _sat;

}


int LinearBblast::show_problem(){

	printf("\e[33m ==== Constraints: \e[0m\n");
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("  %s\n", smt2_representation(*it).c_str());
	}

	getchar();
}


bool LinearBblast::solvable_problem(){
	return sat;
}


void LinearBblast::propagate_unary_extra(string src, string dst, bool forcedfree){

	if(!islinear(src)){
		set_non_linear(dst);
	}

	//printf("propagate_unary_extra %s %s\n", variables[src].type_rep.c_str(), variables[dst].type_rep.c_str());

	if(variables[dst].type_rep == "")
		variables[dst].type_rep = variables[src].type_rep;
	//variables[dst].type_rep = get_rep_type(src);
}

string LinearBblast::biggest_type(string type1, string type2){
	if(bits(type1) > bits(type2))
		return type1;
	else
		return type2;
}

string LinearBblast::get_rep_type(string varname){

	if(is_constant(varname)){
		return gettype(varname);
	} else {
		if(variables[varname].type_rep != ""){
			return variables[varname].type_rep;
		} else {
			return gettype(varname);
		}
	}

	

}

void LinearBblast::propagate_binary_extra(string op1, string op2, string dst){


	if(!islinear(op1) || !islinear(op2) || !proplinear ) 
		set_non_linear(dst);
	else
		variables[dst].islinear = variables[op1].islinear && variables[op2].islinear;

	if(variables[dst].type_rep == "")
		variables[dst].type_rep = biggest_type(get_rep_type(op1), get_rep_type(op2));
}


void LinearBblast::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");

}


bool LinearBblast::islinear(string varname){
	if( is_constant(varname) || get_is_propagated_constant(varname))
		return true;
	else
		return variables[varname].islinear && variables_generic[varname].type != "FloatTyID" && variables_generic[varname].type != "DoubleTyID";

}



void LinearBblast::add_eq_zero(string variable){

	LinearVarBb var = variables[variable];
	var.polarity = "=";

	printf("\e[32m add_eq_zero \e[0m %s %s\n", variable.c_str(), smt2_representation(var).c_str());


	conditions.push_back( var );
}


void LinearBblast::add_neq_zero(string variable){

	LinearVarBb var = variables[variable];
	var.polarity = "#";

	printf("\e[32m add_neq_zero \e[0m %s %s\n", variable.c_str(), smt2_representation(var).c_str());


	conditions.push_back( var );
	

}


void LinearBblast::dump_conditions(stringstream& sstream){

		assert(0 && "Not Implemented");

}


void LinearBblast::dump_model(){

	assert(0 && "Not implemented");

}


map<set<pair <string, int> >, int> LinearBblast::get_map_idx_val(string name){
	assert(0 && "Not Implemented");
}



void LinearBblast::add_eq_set(set<pair <string, int> > set_idx_val){
	assert(0 && "Not Implemented");
}



void LinearBblast::set_content(string name, string value){

	assert(0 && "not implemented");

}


string LinearBblast::eval(string expression){
	assert(0 && "Not Implemented");
}


void LinearBblast::add_bt(string var, string val){

	assert(0 && "Not Implemented");

}

void LinearBblast::add_lt(string var, string val){

	assert(0 && "Not Implemented");

}

pair<int, int> LinearBblast::get_range(string name){

	assert(0 && "Not Implemented");

}





bool LinearBblast::empty_assertions(){

	assert(0 && "Not Implemented");

}


void LinearBblast::add_smt(string smt){

	assert(0 && "Not Implemented");

}
