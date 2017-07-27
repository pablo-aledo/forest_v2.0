/*
 * =====================================================================================
 * /
 * |     Filename:  measurement.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/26/2013 09:22:48 AM
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


#include "measurement.h"
#include "utils.h"
#include "database.h"
#include <stdlib.h>

using namespace std;

#define debug true

#define UNDERSCORE "_"


extern Database* database;

Measurement::Measurement(){
	branches_count = 0;
}

Measurement::~Measurement(){
	
}

void Measurement::begin_bb(char* _name){

	string name = string(_name);

	visited_bbs.insert(actual_fn_name + UNDERSCORE + name);

	debug && printf("\e[31m begin_bb %s \e[0m\n", _name );
}

void Measurement::end_bb(char* name){
	//debug && printf("\e[31m end_bb %s\e[0m\n", name );
}

map<string, vector<string> > Measurement::load_test_vectors(){

	debug && printf("load_test_vectors\n");

	vector<string> free_variables;
	map<string, vector<string> > ret;

	FILE* file;




{

		ifstream input("free_variables");
		string line;
		
		while( getline( input, line ) ) {
			vector<string> tokens = tokenize(line, " ");
			string name = tokens[0];
	
			free_variables.push_back(name);
		}

		if(!free_variables.size()) exit(0);
		
}
	debug && printf("loading free_variables %lu\n", free_variables.size()); fflush(stdout);
	



{
		ifstream input("vectors");
		string line;
		
		while( getline( input, line ) ) {
			
			vector<string> tokens = tokenize(line, " ");

			assert(tokens.size() == free_variables.size() && "Different number of tokens in vector and free_variables");
	
			for ( unsigned int i = 0; i < tokens.size(); i++) {
				debug && printf("load_vector %s %s\n", free_variables[i].c_str(), tokens[i].c_str() );
				ret[ free_variables[i] ].push_back(tokens[i]);
			}
		}

		debug && printf("loading test_vectors %lu\n", ret[ free_variables[0] ].size()); fflush(stdout);
}
	


	debug && printf("End_loading\n"); fflush(stdout);

	return ret;
	
}

int Measurement::vector_int(char* _name){
	
	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_int %s %s\n", _name, ret.c_str());

	return stoi(ret);
}

float Measurement::vector_float(char* _name){
	
	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_float %s %s\n", _name, ret.c_str());

	return stof(ret);
}

short Measurement::vector_short(char* _name){

	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_short %s %s\n", _name, ret.c_str());

	short ret_s = stos(ret);

	return ret_s;
}


long Measurement::vector_long(char* _name){

	string name = string(_name);


	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_long %s %s\n", _name, ret.c_str());

	long ret_l = stoi(ret);

	return ret_l;
}


char Measurement::vector_char(char* _name){

	string name = string(_name);

	string ret = test_vectors[string(name)][0];
	test_vectors[string(name)].erase(test_vectors[string(name)].begin());

	debug && printf("vector_char %s %s\n", _name, ret.c_str());

	char ret_c = stoc(ret);

	return ret_c;
}

void Measurement::begin_sim_measurement(char* functions, char* bbs){

	database->start_database_measurement();
	test_vectors = load_test_vectors();

	{
		debug && printf("Inserting functions %s\n", functions);
		vector<string> tokens = tokenize(functions, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			//if( *it == "test"       ) continue;
			//if( *it == "begin_bb"   ) continue;
			//if( *it == "end_bb"     ) continue;
			//if( *it == "BeginFn"    ) continue;
			//if( *it == "vector_int" ) continue;
			debug && printf("Insert_fn %s\n", it->c_str());
			available_fns.insert(*it);
		}
	}
	

	{
		debug && printf("Inserting bbs %s\n", bbs);
		vector<string> tokens = tokenize(bbs, ",");
	
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			//if( *it == "main_entry" ) continue;
			//if( *it == "main_bb" ) continue;
			//if( *it == "main_bb2" ) continue;
			debug && printf("Insert_bb %s\n", it->c_str());
			available_bbs.insert(*it);
		}
	}

	debug && printf("\e[31m Begin Measurement\e[0m %s %s\n", functions, bbs );
}

void Measurement::BeginFn(char* _fn_name){

	debug && printf("\e[31m begin_fn %s \e[0m\n", _fn_name);
	string function_name = string(_fn_name);

	actual_fn_name = function_name;

	fn_stack.push_back(function_name);

	visited_fns.insert(function_name);



}

void Measurement::EndFn(){

	debug && printf("\e[31m end_fn %lu \e[0m\n", fn_stack.size());
	assert(fn_stack.size() && "Empty stack");


	printf("size %lu\n", fn_stack.size());
	fn_stack.erase(fn_stack.end()-1);

	if(fn_stack.size()){
		string function_name = fn_stack[fn_stack.size()-1];
		actual_fn_name = function_name;
	}



}

void Measurement::br_instr_cond_measurement(bool value){

	printf("br_instr_cond_measurement %d\n", value);

	path_stack.push_back(value);
	database->insert_problem_measurement();

}

void Measurement::end_sim(){

	debug && printf("visited fns %lu/%lu\n", visited_fns.size(), available_fns.size() );
	debug && printf("visited bbs %lu/%lu\n", visited_bbs.size(), available_bbs.size() );

	debug && printf("visited_fns\n");
	for( set<string>::iterator it = visited_fns.begin(); it != visited_fns.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	debug && printf("available_fns\n");
	for( set<string>::iterator it = available_fns.begin(); it != available_fns.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	
	debug && printf("visited_bbs\n");
	for( set<string>::iterator it = visited_bbs.begin(); it != visited_bbs.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");


	debug && printf("available_bbs\n");
	for( set<string>::iterator it = available_bbs.begin(); it != available_bbs.end(); it++ ){
		debug && printf("%s,", it->c_str() );
	} debug && printf("\n");



	stringstream value;

	value.str("");
	value << visited_fns.size() << "/" << available_fns.size() << " ( " <<
		(int)(100.0*(float)visited_fns.size()/(float)available_fns.size())
		<< " % )";

	database->insert_measurement("visited_fns", value.str());

	value.str("");
	value << visited_bbs.size() << "/" << available_bbs.size() << " ( " <<
		(int)(100.0*(float)visited_bbs.size()/(float)available_bbs.size())
		<< " % )";
	database->insert_measurement("visited_bbs", value.str());

	database->end_database_measurement();

	debug && printf("\e[31m End Simulation\e[0m\n---------------------------------------------\n" );
	

}

void Measurement::br_count(){
	branches_count++;
}

void Measurement::end_count(){
	printf("Number of branches %d\n", branches_count);

}

