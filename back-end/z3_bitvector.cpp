/*
 * =====================================================================================
 * /
 * |     Filename:  z3_bitvector.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/02/2014 09:30:47 AM
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


#include "z3_bitvector.h"
#include "options.h"
#include "operators.h"
#include "database.h"
#include "timer.h"
#include "utils.h"
#include "architecture.h"

extern Options* options;
extern Operators* operators;
extern Database* database;
extern Timer* timer;

Z3BitVector::Z3BitVector(){
	
}

Z3BitVector::~Z3BitVector(){
	
}

void Z3BitVector::dump_problem(string& filename_base){

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		internal_condition(it->position).c_str();
	}
	for( map<string,Z3Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		if(!need_for_dump(it->first, it->second.content)) continue;
		internal_condition(it->second.content);
	}

	FILE* file = fopen(filename_base.c_str(), "w");
	dump_header(file);
	dump_variables(file);
	dump_extra(file);
	dump_conditions(file);
	dump_check_sat(file);
	dump_get(file);
	dump_tail(file);
	fclose(file);

}

void Z3BitVector::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");

}

void Z3BitVector::dump_variables(FILE* file){

	//// try to avoid returning if not free variables !
	
	//if(!free_variables.size()){
	//	printf("Empty_free_variables\n");
	//	assert(0 && "Empty free_variables");
	//}

	if(!free_variables.size()) return;
	assert(free_variables.size() && "Empty free_variables");

	//printf("\e[31m Dump_variables free_variables.size() %lu\e[0m\n", free_variables.size() );


	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);
		int bits;

		assert(position != "" && "Unknown variable");
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
		} else if(type == "PointerTyID") {
			bits = 64;
			fprintf(file,"(declare-const %s (_ BitVec %d))\n", position.c_str(), bits);
		} else {
			if(isdriver) assert(0 && "Unknown Type");
		}

	}
	

}


string Z3BitVector::canonical_representation(string in){

	//printf("canonical_representation in %s\n", in.c_str() ); fflush(stdout);
	if(in[0] != '#' && in != "true" && in != "false" && in.find(".") == string::npos )
		assert(0 && "Canonical_Representation of a non-internal");


	if(in == "false") return "false";
	if(in == "true") return "true";

	int a;
	char ret_str[10];
	sscanf(in.substr(2).c_str(), "%x", &a);
	sprintf(ret_str, "%d", a);

	//printf("canonical_representation in %s a %d ret %s\n", in.c_str(), a, ret_str );

	return string(ret_str);
}

string Z3BitVector::internal_representation(int in, string type){
	return hex_representation_2(in, type);
}

void Z3BitVector::dump_extra(FILE* file){
}




map<set<pair<string, int> > , int > Z3BitVector::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){

	debug && printf("\e[32m get_idx_val %s %d %d %lu\e[0m\n", base.c_str(), first_address, last_address, indexes.size());
	


	set<string> index_vars = variables[base].indexes;
	for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
		debug && printf("\e[32m index \e[0m %s\n", it->c_str());

		set<string> indexes_index = variables[*it].indexes;
		for( set<string>::iterator it2 = indexes_index.begin(); it2 != indexes_index.end(); it2++ ){
			debug && printf("\e[32m index2 \e[0m %s\n", variables_generic[*it2].name_hint.c_str() );
			index_vars.insert( variables_generic[*it2].name_hint );
		}
	}
	
	map<set<pair<string, int> > , int > ret;

	bool is_sat;

	string idx_show;
	for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
		idx_show += *it + ",";
	}
	

	//idx_content = internal_condition(idx_content);
	
	printf("\e[32m base \e[0m %s \e[32m idx_content \e[0m %s \e[32m indexes \e[0m %s \e[32m first_address \e[0m %d \e[32m last_address \e[0m %d\n", base.c_str(), idx_content.c_str(), idx_show.c_str(), first_address, last_address);

	int iters = 0;
	while(true){

		static int count;
		printf("ITERATION %d\n", count++);


		FILE* ftmp = fopen(tmp_file("idx_problem.smt2").c_str(), "w");
		fprintf(ftmp, "(set-option :produce-models true)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			printf("getting type of %s from hint %s\n", find_by_name_hint(*it).c_str() , it->c_str()  );

			//string type = gettype("mem_" + realvalue(find_by_name_hint(*it)));
			string type = gettype(find_by_name_hint(*it));

			fprintf(ftmp, "(declare-const %s (_ BitVec %d))\n", it->c_str(), bits(type)  );
		}

		stringstream excl_expr;
		stringstream range_expr;

		range_expr << "(and " << "(bvsle " << "constant_PointerTyID_" << first_address << " " << idx_content << ") " << "(bvsle " << idx_content << " " << "constant_PointerTyID_" << last_address << "))";


		set<set<pair<string, int> > > exclusions = get_exclusions(ret);

		//printf("exclusions.size() %d\n", exclusions.size() );

		excl_expr << "(not ";
		if(exclusions.size() > 1)
			excl_expr << "(or ";
		for( set<set<pair<string, int> > >::iterator it = exclusions.begin(); it != exclusions.end(); it++ ){
			set<pair<string, int> > fsol = (*it);
			if(fsol.size() > 1)
				excl_expr << "(and ";
			for( set<pair<string, int> >::iterator it2 = fsol.begin(); it2 != fsol.end(); it2++ ){

				//excl_expr << "(= " << it2->first << " " << "constant_" << gettype("mem_" + realvalue(find_by_name_hint(it2->first))) << "_" << it2->second << ") ";
				excl_expr << "(= " << it2->first << " " << "constant_" << gettype(find_by_name_hint(it2->first)) << "_" << it2->second << ") ";

			}
			if(fsol.size() > 1)
				excl_expr << ")";
		}
		if(exclusions.size() > 1)
			excl_expr << ")";
		excl_expr << ")";



		fprintf(ftmp, "(assert %s)\n", internal_condition(range_expr.str()).c_str());

		if(exclusions.size() > 0)
			fprintf(ftmp, "(assert %s)\n", internal_condition(excl_expr.str()).c_str());






		fprintf(ftmp, "(check-sat)\n");

		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			fprintf(ftmp, "(get-value (%s))\n", internal_condition(*it).c_str());
		}

		fprintf(ftmp, "(get-value (%s))\n", internal_condition(idx_content).c_str() );

		fclose(ftmp);

		system(("z3_timed 60 " + tmp_file("idx_problem.smt2") + " > " + tmp_file("idx_out")).c_str());


		ifstream input(tmp_file("idx_out").c_str());
		string line;
		vector<string> result;

		while( getline( input, line ) ) {
			result.push_back(line);
		}


		if(result[0].find("error") != string::npos ){
			printf("Error in z3 execution\n");
			solve_problem();
			assert(0 && "Error in z3 execution");
		}


		is_sat = (result[0] == "sat");

		if(!is_sat){
			//printf("no sat\n");
			break;
		}

		if(iters++ == options->cmd_option_int("max_pointer_deref_combs")){
			printf("number of iterations exceeded\n");
			break;
		}

		set<pair<string, int> > sub_sol;

		int i = 0;
		for( set<string>::iterator it = index_vars.begin(); it != index_vars.end(); it++ ){
			i++;
			string line = result[i];
			if(line.find("error") != string::npos )
				assert(0 && "Error in z3 execution");

			string varname = *it;
			string value = canonical_representation(result_get(line));
			printf("value_canonical_rep %s\n", value.c_str());

			sub_sol.insert(pair<string, int>(varname, stoi(value)));

		}
		
		i++;
		line = result[i];
		int idx_res = stoi(canonical_representation(result_get(line)));

		//printf("idx_res %d\n", idx_res);

		ret[sub_sol] = idx_res;

		//static int p;
		//if(p++ == 3) break;

	}

	//for( set<pair<string, int> >::iterator it = sub_sol.begin(); it != sub_sol.end(); it++ ){
		//printf("sub_sol %s %d\n", it->first.c_str(), it->second);
	//}
	
	
	return ret;
	//exit(0);

}


void Z3BitVector::representation_constants(string& condition){


	vector<string> types;
	types.push_back("IntegerTyID32");
	types.push_back("IntegerTyID16");
	types.push_back("IntegerTyID64");
	types.push_back("IntegerTyID8");
	types.push_back("DoubleTyID");
	types.push_back("PointerTyID");
	types.push_back("Pointer");


	for( vector<string>::iterator it = types.begin(); it != types.end(); it++ ){

		string subst = "constant_" + *it + "_";

		while(true){

			if( condition.find(subst) == string::npos ){
				break;
			} else {
				string before = condition.substr(0, condition.find(subst) );
				string substr = tokenize(condition.substr(condition.find(subst) ), "() ")[0];
				string after  = condition.substr( before.length() + substr.length() );

				string type  = tokenize(substr, "_")[1];
				string value = tokenize(substr, "_")[2];

				assert(is_number(value) && "Value is not a number");

				int value_i = stoi(value);


				//printf("\e[32m before \e[0m .%s.\n", before.c_str());
				//printf("\e[32m substr \e[0m .%s.\n", substr.c_str());
				//printf("\e[32m after  \e[0m .%s.\n", after.c_str());



				condition = before + internal_representation(value_i, type) + after;

				//printf("condition %s\n", condition.c_str());

			}

		}
	}
/*

	string subst = "constant_FloatTyID_";

	while(true){

		if( condition.find(subst) == string::npos ){
			break;
		} else {
			string before = condition.substr(0, condition.find(subst) );
			string substr = tokenize(condition.substr(condition.find(subst) ), "() ")[0];
			string after  = condition.substr( before.length() + substr.length() );

			string type  = tokenize(substr, "_")[1];
			string value = tokenize(substr, "_")[2];

			assert(is_number(value) && "Value is not a number");

			//printf("\e[32m before \e[0m .%s.\n", before.c_str());
			//printf("\e[32m substr \e[0m .%s.\n", substr.c_str());
			//printf("\e[32m after  \e[0m .%s.\n", after.c_str());


			//condition = before + internal_representation(value_i, type) + after;
			condition = before + "((_ asFloat 11 53) roundTowardZero " + value + " 0)" + after;

			//printf("condition %s\n", condition.c_str());

		}

	}

*/



}


void Z3BitVector::get_operands(string condition, string operation, string& substr, string& before, string& after, string& param){

		int ini = condition.find("(" + operation + " ");

		substr = close_str(condition.substr(ini));

		before = condition.substr(0, ini);
		after = condition.substr(before.length() + substr.length() );

		//param1 = parameter(substr.substr(4));
		param = parameter(substr.substr(2+operation.length()));

		//debug && printf("\e[32m get_operands \e[0m \e[32m ini \e[0m %d \e[32m operation \e[0m %s \e[32m substr \e[0m .%s. \e[32m before \e[0m .%s. \e[32m after \e[0m .%s.\n", ini, operation.c_str(), substr.c_str(), before.c_str(), after.c_str());
		//debug && printf("\e[32m param \e[0m .%s.\n", param.c_str());
}

void Z3BitVector::change_cast(string& condition){

	while(true){

	if( condition.find("cast") == string::npos ){
		return;
	} else {

		assert(condition.find("__") == string::npos && "Undefined casting");

		string castop = tokenize(condition.substr(condition.find("cast_")), " ")[0];

		string substr, before, after, param;
		get_operands(condition, castop, substr, before, after, param);
		
		string ext_type = tokenize(castop, "_")[1];
		string type_src = tokenize(castop, "_")[2];
		string type_dst = tokenize(castop, "_")[3];

		int bits_src = bits(type_src);
		int bits_dst = bits(type_dst);
		int diff = bits_dst - bits_src;

		if( diff > 0 ){
			//string content_dst = "(concat " + concat_begin(bits_dst - bits_src, 0) + " " + param + ")";
			string content_dst;
			if(ext_type == "s")
				content_dst = "(concat " + sign_ext(bits_src, bits_dst, param) + " " + param + ")";
			else
				content_dst = "(concat " + zero_ext(bits_src, bits_dst, param) + " " + param + ")";

			condition = before + content_dst + after;
			printf("condition_1 %s\n", condition.c_str());

			//exit(0);
		}

		if( diff < 0 ){
			string content_dst = "((_ extract " + itos(bits(type_dst)-1) + " 0) " + param + ")";
			condition = before + content_dst + after;
			printf("condition_2 %s\n", condition.c_str());
			//exit(0);
		}

		if( diff == 0 ){
			condition = before + param + after;
			//printf("condition_2 %s\n", condition.c_str());
		}




	}

	}
}



void Z3BitVector::get_name(string& filename){
	vector<string> tokens = tokenize(filename, "_.");
	filename = tokens[0] + "_bitvector_" + tokens[1] + "." + tokens[2];
}




void Z3BitVector::replace_and(string& condition){
	vector<int> widths;
	widths.push_back(8);
	widths.push_back(16);
	widths.push_back(32);
	widths.push_back(64);

	for ( unsigned int i = 0; i < widths.size(); i++) {
		
	int width = widths[i];
	string operand = "Y" + itos(width);
	while(true){

	if( condition.find(operand) == string::npos ){
		break;
	} else {

		string uniq_id;
		string::iterator it = condition.begin() + condition.find(operand) + operand.length() + 1;
		while(*it != ' '){
			uniq_id += *it;
			it++;
		}

		string operand_with_id = operand + "_" + uniq_id;

		myReplace(condition, "(" + operand_with_id , "(bvand");


	}
	}
	}
}

void Z3BitVector::replace_or(string& condition){
	vector<int> widths;
	widths.push_back(8);
	widths.push_back(16);
	widths.push_back(32);
	widths.push_back(64);

	for ( unsigned int i = 0; i < widths.size(); i++) {
		
	int width = widths[i];
	string operand = "O" + itos(width);
	while(true){

	if( condition.find(operand) == string::npos ){
		break;
	} else {

		string uniq_id;
		string::iterator it = condition.begin() + condition.find(operand) + operand.length() + 1;
		while(*it != ' '){
			uniq_id += *it;
			it++;
		}

		string operand_with_id = operand + "_" + uniq_id;

		myReplace(condition, "(" + operand_with_id , "(bvor");


	}
	}
	}
}

string Z3BitVector::internal_condition(string condition){

	remv_op_constant(condition);
	change_cast(condition);
	representation_constants(condition);
	myReplace(condition, "(* ",  "(bvmul ");
	myReplace(condition, "(*f ",  "(bvmul ");
	myReplace(condition, "(*c ",  "(bvmul ");
	myReplace(condition, "(*fc ",  "(bvmul ");
	myReplace(condition, "(+ ",  "(bvadd ");
	myReplace(condition, "(- ",  "(bvsub ");
	myReplace(condition, "(/ ",  "(bvudiv ");
	myReplace(condition, "(% ",  "(bvsmod ");
	myReplace(condition, "(u% ",  "(bvumod ");
	myReplace(condition, "(u< " , "(bvult ");
	myReplace(condition, "(u> " , "(bvugt ");
	myReplace(condition, "(u<= ", "(bvule ");
	myReplace(condition, "(u>= ", "(bvuge ");
	myReplace(condition, "(<= ", "(bvsle ");
	myReplace(condition, "(>= ", "(bvsge ");
	myReplace(condition, "(> ",  "(bvsgt ");
	myReplace(condition, "(< ",  "(bvslt ");
	myReplace(condition, "(X ",  "(bvxor ");
	myReplace(condition, "(>> ", "(bvlshr ");
	myReplace(condition, "(<< ", "(bvshl ");
	myReplace(condition, "(Y32 ",  "(bvand ");
	myReplace(condition, "(O ",  "(bvor ");
	myReplace(condition, "constant_bool_true",  "true");
	myReplace(condition, "constant_bool_false",  "false");
	replace_and(condition);
	replace_or(condition);
	return condition;

}


bool Z3BitVector::islinear(string varname){
	if( is_constant(varname) || get_is_propagated_constant(varname))
		return true;
	else
		return variables[varname].islinear && variables_generic[varname].type != "FloatTyID" && variables_generic[varname].type != "DoubleTyID";

}

string Z3BitVector::eval(string expression){


	return "";
	myReplace(expression, "return_of___VERIFIER_nondet_char_1", "#x00");
	myReplace(expression, "return_of___VERIFIER_nondet_char_2", "#x00");
	myReplace(expression, "return_of___VERIFIER_nondet_char_3", "#x00");
	myReplace(expression, "return_of___VERIFIER_nondet_char_4", "#x00");
	myReplace(expression, "return_of___VERIFIER_nondet_char"  , "#x00");


	myReplace(expression, "main_register_retval"  , "#x00");


	srand(clock());
	stringstream name_smtfile;
	name_smtfile << tmp_file("eval_") << rand() << ".smt2";
	printf("name_smtfile %s\n", name_smtfile.str().c_str());

	FILE* file = fopen(name_smtfile.str().c_str(), "w");
	fprintf(file, "(set-option :produce-models true)\n");
	fprintf(file, "(check-sat)\n");
	fprintf(file, "(get-value (%s))\n", internal_condition(expression).c_str());
	fclose(file);

	system(("z3 " + name_smtfile.str() + " > " + tmp_file("eval_out")).c_str());

	ifstream input(tmp_file("eval_out").c_str());
	string line;
	
	getline( input, line );
	getline( input, line );

	string value = canonical_representation(result_get(line));
		
	return value;
}


