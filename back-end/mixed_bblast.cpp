/*
 * =====================================================================================
 * /
 * |     Filename:  mixed_bblast.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/13/2014 04:07:21 PM
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

#include "mixed_bblast.h"
#include "architecture.h"

MixedBblast::MixedBblast(){
	
}

MixedBblast::~MixedBblast(){
	
}


string MixedBblast::type_free_var(string name_hint){

	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){

		string position = it->position;
		string type = gettype(it->name);

		if(position == name_hint)
			return type;
	}

	for( vector<BoolVar>::iterator it = bits.begin(); it != bits.end(); it++ ){

		string name = it->name;
		string type = it->type;

		if(name == name_hint)
			return type;
	}

	for( vector<AuxVar>::iterator it = aux_vars.begin(); it != aux_vars.end(); it++ ){
		string name = it->name;
		string type = it->type;


		if( name == name_hint ){
			return type;
		}
	}

	if(isdriver)assert(0 && "Variable not found");

}




void MixedBblast::and_operation(string op1, string op2, string dst){

	// As I'm using this variables directly below, they need to be 
	// correctly initialized. This is important with constants, that
	// are not already present in 'variables' map.
	if(variables[op1].type_rep == ""){
		variables[op1].type_rep = gettype(op1);
	}
	if(variables[op2].type_rep == ""){
		variables[op2].type_rep = gettype(op2);
	}
	if(variables[op1].content.size() == 0){
		variables[op1].content = content(op1);
	}
	if(variables[op2].content.size() == 0){
		variables[op2].content = content(op2);
	}


	int uniq = rand();

	printf("mixedbblast_and_operation\n");
	variables[dst].content["z" + itos(uniq)] = HexNum(1);

	BoolVar bool_var = {"z" + itos(uniq), gettype(op1)};
	bits.push_back(bool_var);

	stringstream bit_op;
	bit_op << "(= z" << uniq << " (bvand " << smt2_representation(variables[op1]) << " " << smt2_representation(variables[op2]) << "))";
	bit_conditions.push_back(bit_op.str());

}



void MixedBblast::or_operation(string op1, string op2, string dst){

	// As I'm using this variables directly below, they need to be 
	// correctly initialized. This is important with constants, that
	// are not already present in 'variables' map.
	if(variables[op1].type_rep == ""){
		variables[op1].type_rep = gettype(op1);
	}
	if(variables[op2].type_rep == ""){
		variables[op2].type_rep = gettype(op2);
	}
	if(variables[op1].content.size() == 0){
		variables[op1].content = content(op1);
	}
	if(variables[op2].content.size() == 0){
		variables[op2].content = content(op2);
	}


	int uniq = rand();

	printf("mixedbblast_or_operation\n");
	variables[dst].content["z" + itos(uniq)] = HexNum(1);

	BoolVar bool_var = {"z" + itos(uniq), gettype(op1)};
	bits.push_back(bool_var);

	stringstream bit_op;
	bit_op << "(= z" << uniq << " (bvor " << smt2_representation(variables[op1]) << " " << smt2_representation(variables[op2]) << "))";
	bit_conditions.push_back(bit_op.str());

}



void MixedBblast::dump_bit_operations(FILE* file){

	for( vector<string>::iterator it = bit_conditions.begin(); it != bit_conditions.end(); it++ ){
		
		fprintf(file,"(assert %s)\n", it->c_str());
	}
	

}


void MixedBblast::dump_bits(FILE* file){

	for( vector<BoolVar>::iterator it = bits.begin(); it != bits.end(); it++ ){
		
		fprintf(file,"(declare-const %s (_ BitVec %d))\n", it->name.c_str(), get_n_bits(it->type));
	}
	

}


void MixedBblast::dump_problem(string filename){


		FILE* file = fopen( filename.c_str(), "w");



		dump_header(file);
		dump_free_variables(file);
		dump_aux_variables(file);
		dump_bits(file);
		dump_bit_operations(file);
		dump_constraints(file);
		dump_check_sat(file);
		dump_get(file);
		dump_tail(file);
		dump_statistics(file);

		fclose(file);



}


void MixedBblast::dump_statistics(FILE* file){
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



	int maxterms = 0;
	float avgterms = 0;
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		if( it->content.size() > maxterms ) maxterms = it->content.size();
		avgterms += (float)(it->content.size());
	}
	avgterms /= (float)(conditions.size());


	fprintf(file, "; N_TERM_MAX_B %d\n", maxterms );
	fprintf(file, "; N_TERM_AVG %.3f\n", avgterms );


	float nbits = 0;
	for( vector<BoolVar>::iterator it = bits.begin(); it != bits.end(); it++ ){
		nbits += get_n_bits(it->type);
	}
	nbits = bits.size()?nbits/(float)(bits.size()):0;
	

	fprintf(file, "; BITS %.3f\n", nbits);
	fprintf(file, "; BOOL_WORDS %lu\n", bits.size());
}

void MixedBblast::get_name(string& filename){

	vector<string> tokens = tokenize(filename, "_.");
	filename = "z3_mixedbblast_" + tokens[2] + ".smt2";

}


int MixedBblast::show_problem(){

	printf("\e[33m ==== Constraints: \e[0m\n");
	for( vector<LinearVarBb>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
		printf("  %s\n", smt2_representation(*it).c_str());
	}

	for( vector<string>::iterator it = bit_conditions.begin(); it != bit_conditions.end(); it++ ){
		printf("  %s\n", it->c_str());
	}
	

	getchar();
}





void MixedBblast::dump_model(){

	assert(0 && "Not implemented");

}
