/*
 * =====================================================================================
 * /
 * |     Filename:  mixed_int.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/10/2014 10:38:46 AM
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

#include "mixed_int.h"

MixedInt::MixedInt(){
}

MixedInt::~MixedInt(){
	
}

void MixedInt::dump_header(FILE* file){

	fprintf(file,"(set-option :produce-models true)\n");
	fprintf(file,"(set-option :pp-decimal true)\n");
	if(bit_conditions.size() == 0)
		fprintf(file,"(set-logic AUFLIRA)\n");
	else 
		fprintf(file,"(set-logic AUFNIRA)\n");

}

void MixedInt::and_operation(string op1, string op2, string dst){

	if( !variables[op1].content.size() ) variables[op1].content = content(op1);
	if( !variables[op2].content.size() ) variables[op2].content = content(op2);

	assert(variables[op1].content.size() && "Operand 1 empty");
	assert(variables[op2].content.size() && "Operand 2 empty");




	printf("mixed_and_operation\n");

	int width = get_n_bits(gettype(op1));

	int uniq_num = rand();

	LinearVariable ret;
	for ( unsigned int i = 0; i < width; i++) {
		bits.push_back( "x" + itos(uniq_num) + itos(i) );
		bits.push_back( "y" + itos(uniq_num) + itos(i) );
		bits.push_back( "z" + itos(uniq_num) + itos(i) );
		
		int exp = 1 << i;
		ret.content["z" + itos(uniq_num) + itos(i)] = exp;
	}
	variables[dst].content = ret.content;


	LinearVariable eq1;
	for ( unsigned int i = 0; i < width; i++) {
		int exp = 1 << i;
		eq1.content["x" + itos(uniq_num) + itos(i)] = exp;
	}
	map<string, float> op1c = variables[op1].content;
	for( map<string,float>::iterator it = op1c.begin(); it != op1c.end(); it++ ){
		eq1.content[it->first] -= it->second;
	}
	eq1.polarity = "=";
	conditions.push_back(eq1);




	LinearVariable eq2;
	for ( unsigned int i = 0; i < width; i++) {
		int exp = 1 << i;
		eq2.content["y" + itos(uniq_num) + itos(i)] = exp;
	}
	map<string, float> op2c = variables[op2].content;
	for( map<string,float>::iterator it = op2c.begin(); it != op2c.end(); it++ ){
		eq2.content[it->first] -= it->second;
	}
	eq2.polarity = "=";
	conditions.push_back(eq2);


	printf("\e[32m add constraint \e[0m %s\n", smt2_representation(eq1).c_str());
	printf("\e[32m add constraint \e[0m %s\n", smt2_representation(eq2).c_str());



	for ( unsigned int i = 0; i < width; i++) {
		stringstream bit_comp;
		bit_comp << "(= z" << uniq_num << i << " (* " << "x" << uniq_num << i << " " << "y" << uniq_num << i << "))";
		bit_conditions.push_back(bit_comp.str());
	}


}

void MixedInt::or_operation(string op1, string op2, string dst){


	if( !variables[op1].content.size() ) variables[op1].content = content(op1);
	if( !variables[op2].content.size() ) variables[op2].content = content(op2);



	assert(variables[op1].content.size() && "Operand 1 empty");
	assert(variables[op2].content.size() && "Operand 2 empty");

	printf("mixed_or_operation\n");


	int width = get_n_bits(gettype(op1));

	int uniq_num = rand();

	LinearVariable ret;
	for ( unsigned int i = 0; i < width; i++) {
		bits.push_back( "x" + itos(uniq_num) + itos(i) );
		bits.push_back( "y" + itos(uniq_num) + itos(i) );
		bits.push_back( "z" + itos(uniq_num) + itos(i) );
		
		int exp = 1 << i;
		ret.content["z" + itos(uniq_num) + itos(i)] = exp;
	}
	variables[dst].content = ret.content;


	LinearVariable eq1;
	for ( unsigned int i = 0; i < width; i++) {
		int exp = 1 << i;
		eq1.content["x" + itos(uniq_num) + itos(i)] = exp;
	}
	map<string, float> op1c = variables[op1].content;
	for( map<string,float>::iterator it = op1c.begin(); it != op1c.end(); it++ ){
		eq1.content[it->first] -= it->second;
	}
	eq1.polarity = "=";
	conditions.push_back(eq1);




	LinearVariable eq2;
	for ( unsigned int i = 0; i < width; i++) {
		int exp = 1 << i;
		eq2.content["y" + itos(uniq_num) + itos(i)] = exp;
	}
	map<string, float> op2c = variables[op2].content;
	for( map<string,float>::iterator it = op2c.begin(); it != op2c.end(); it++ ){
		eq2.content[it->first] -= it->second;
	}
	eq2.polarity = "=";
	conditions.push_back(eq2);

	printf("\e[32m add constraint \e[0m %s\n", smt2_representation(eq1).c_str());
	printf("\e[32m add constraint \e[0m %s\n", smt2_representation(eq2).c_str());


	for ( unsigned int i = 0; i < width; i++) {
		stringstream bit_comp;
		stringstream prod;
		stringstream sum;
		stringstream sub;
		sum  << "(+ " << "x" << uniq_num << i << " " << "y" << uniq_num << i << ")";
		prod << "(* " << "x" << uniq_num << i << " " << "y" << uniq_num << i << ")";
		sub  << "(- " << sum.str() << " " << prod.str() << ")";
		bit_comp << "(= z" << uniq_num << i << " " << sub.str() << ")";
		bit_conditions.push_back(bit_comp.str());
	}


}

void MixedInt::dump_bits(FILE* file){

	for( vector<string>::iterator it = bits.begin(); it != bits.end(); it++ ){
		
		fprintf(file,"(declare-fun %s () Int)\n", it->c_str());
	}
	

}

void MixedInt::dump_bit_operations(FILE* file){

	for( vector<string>::iterator it = bit_conditions.begin(); it != bit_conditions.end(); it++ ){
		
		fprintf(file,"(assert %s)\n", it->c_str());
	}
	

}

void MixedInt::dump_bit_limits(FILE* file){

	for( vector<string>::iterator it = bits.begin(); it != bits.end(); it++ ){
		if((*it)[0] == 'z') continue;
		fprintf(file,"(assert (and (<= 0 %s) (<= %s 1)))\n", it->c_str(), it->c_str() );
	}

}


void MixedInt::dump_aux_variables(FILE* file){
	for( vector<AuxVar>::iterator it = aux_vars.begin(); it != aux_vars.end(); it++ ){
		
		string name = it->name;
		string type = z3_type(it->type);

		fprintf(file,"(declare-fun %s () %s)\n", name.c_str(),type.c_str());
	}
	
}


void MixedInt::dump_problem(string filename){


	printf("mixedint_dump_problem\n");

		FILE* file = fopen( filename.c_str(), "w");



		dump_header(file);
		dump_free_variables(file);
		dump_aux_variables(file);
		dump_bits(file);
		dump_bit_operations(file);
		dump_type_limits(file);
		dump_bit_limits(file);
		dump_constraints(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		dump_statistics(file);

		fclose(file);



}


string MixedInt::smt2_representation(LinearVariable variable){

	map<string, float> content = variable.content;
	string polarity = variable.polarity;

	stringstream ret;

	if(variable.polarity != ""){
		ret << "(" << variable.polarity << " ";
	}

	if(content.size() > 1){
		ret << "(+ ";
		for( map<string,float>::iterator it = content.begin(); it != content.end(); it++ ){

			char second[30];
			sprintf(second, "%.0f", it->second);

			if(it->first == ""){
				ret << second << " ";
			} else {
				if(it->second == 1.0){
					ret << it->first << " ";
				} else {
					ret << "(* " << it->first << " " << second << ") " ;
				}
			}
		}
		ret << ")";

	} else {
		map<string, float>::iterator it = content.begin();
		char second[30];
		sprintf(second, "%.0f", it->second);
		if(it->first == ""){
			ret << second << " ";
		} else {
			if(it->second == 1.0){
				ret << it->first << " ";
			} else {
				ret << "(* " << it->first << " " << second << ") " ;
			}
		}

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

void MixedInt::right_shift(string op1, string op2, string dst){

	string uniq_num = itos(rand());

	if(is_constant(op2) || get_is_propagated_constant(op2)){
		int exponent = 1 << stoi(realvalue(op2));


		map<string, float> content_initial = variables[op1].content;
		map<string, float> content_final;

		content_final["new_var" + uniq_num] = exponent;
		for( map<string,float>::iterator it = content_initial.begin(); it != content_initial.end(); it++ ){
			content_final[it->first] = -content_initial[it->first];
		}
		

		LinearVariable new_restr;
		new_restr.content = content_final;
		new_restr.polarity = "=";
		conditions.push_back(new_restr);

		AuxVar aux_var = {"new_var" + uniq_num, gettype(op1)};
		aux_vars.push_back(aux_var);
		

		variables[dst].content.clear();
		variables[dst].content["new_var" + uniq_num] = 1;

	} else {
		proplinear = false;
	}
}

bool MixedInt::islinear(string varname){
	if( is_constant(varname) || get_is_propagated_constant(varname))
		return true;
	else
		return variables[varname].islinear && variables_generic[varname].type != "FloatTyID" && variables_generic[varname].type != "DoubleTyID";

}

void MixedInt::get_name(string& filename){

	vector<string> tokens = tokenize(filename, "_.");
	filename = "z3_mixedint_" + tokens[2] + ".smt2";

}

void MixedInt::dump_statistics(FILE* file){
	fprintf(file, "; ASSERTIONS %lu\n", conditions.size() );

	int zeros = 0;
	for( vector<LinearVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		for( set<NameAndPosition>::iterator it2 = free_variables.begin(); it2 != free_variables.end(); it2++ ){
			//printf("finding %s in %s\n", it2->position.c_str(), smt2_representation(*it).c_str() );
			if( it->content.find(it2->position) == it->content.end() )
				zeros++;
		}
	}
	fprintf(file, "; ZEROS %d\n", zeros );


	int maxterms = 0;
	float avgterms = 0;
	for( vector<LinearVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->content.size() > maxterms ) maxterms = it->content.size();
		avgterms += (float)(it->content.size());
	}
	avgterms /= (float)(conditions.size());
	fprintf(file, "; N_TERM_MAX_I %d\n", maxterms );
	fprintf(file, "; N_TERM_AVG %.3f\n", avgterms );






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
	fprintf(file, "; BOOL_BITS %lu\n", this->bits.size());

	fprintf(file, "; BOOL_OPS %lu\n", bit_conditions.size());




}


int MixedInt::show_problem(){

	printf("\e[33m ==== Constraints: \e[0m\n");
	for( vector<LinearVariable>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("  %s\n", smt2_representation(*it).c_str());
	}

	for( vector<string>::iterator it = bit_conditions.begin(); it != bit_conditions.end(); it++ ){
		printf("  %s\n", it->c_str());
	}
	

	getchar();
}



