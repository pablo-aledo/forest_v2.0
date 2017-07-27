/*
 * =====================================================================================
 * /
 * |     Filename:  random_testing.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 06:04:06 PM
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

#include "random_testing.h"

void random_testing(){

	gen_file_free_variables_from_xml();
	gen_file_vectors_random();
	gen_final_for_measurement();

	set_option("measurement", "true");
	options_to_file();


	// Run
	
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" + output_file;
	systm(cmd.str().c_str());

}

int custom_random(string name, map<string, string> distributions){


	vector<string> tokens = tokenize( distributions[name], " ");
	string distribution = tokens[0];

	//printf("distribution %s %s\n", name.c_str(), distribution.c_str());

	if( distribution == "uniform" ){

		int min_r = stoi(tokens[1]);
		int max_r = stoi(tokens[2]);
		int ret = (rand() % (max_r-min_r)) + min_r;

		return ret;

	}

	assert(0 && "Unknown distribution");


}

void gen_file_vectors_random(){

	string filename;

	filename = tmp_file("vectors");

	FILE* file = fopen(filename.c_str(), "w");

	vector<string> types;
	vector<string> names;
	vector<string> free_variables = cmd_option_string_vector("random_variable");
	for( vector<string>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");
		types.push_back(tokens[1]);
		names.push_back(tokens[0]);
	}

	map<string, string> distributions_map;
	vector<string> distributions = cmd_option_string_vector("distribution");
	for( vector<string>::iterator it = distributions.begin(); it != distributions.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");

		string distribution;
		for ( unsigned int i = 1; i < tokens.size(); i++) {
			distribution += " " + tokens[i];
		}

		distributions_map[tokens[0]] = distribution;
	}







	for ( unsigned int i = 0; i < cmd_option_int("num_random_vectors"); i++) {
		for ( unsigned int j = 0; j < types.size(); j++) {
			string type = types[j];
			string name = names[j];
			if( type == "Int32" ){
				fprintf(file, "%d ", (int)custom_random(name, distributions_map) );
			} else if( type == "Int16" ){
				fprintf(file, "%d ", (short)custom_random(name, distributions_map) );
			} else if( type == "Int8"){
				fprintf(file, "%d ", (char)custom_random(name, distributions_map) );
			} else {
				assert(0 && "Unknown type");
			}
		}

		fprintf(file, "\n");
		
	}
	



	fclose(file);


}

void gen_file_free_variables_from_xml(){

	vector<string> free_variables = cmd_option_string_vector("random_variable");


	string filename;

	filename = tmp_file("free_variables");

	FILE* file = fopen(filename.c_str(), "w");


	for( vector<string>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		fprintf(file, "%s\n", it->c_str() );
	}

	fclose(file);

}

