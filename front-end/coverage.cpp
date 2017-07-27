/*
 * =====================================================================================
 * /
 * |     Filename:  coverage.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:24:58 PM
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

#include "coverage.h"

#define SIZE_STR 1024

void measure_coverage(){

	start_pass("measure_coverage");

	gen_file_free_variables();
	gen_file_vectors();
	gen_final_for_measurement();

	set_option("measurement", "true");
	options_to_file();

	// Run
	
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());

	end_pass("measure_coverage");
	

}

void check_coverage(){

	start_pass("check_coverage");

	vector<string> coverages;

	coverages.push_back("fn");
	coverages.push_back("bb");

	for( vector<string>::iterator it = coverages.begin(); it != coverages.end(); it++ ){

		string cov = *it;

		int expected_coverage = cmd_option_int("expected_" + cov + "_coverage");

		stringstream cmd;

		// Show results of database
		cmd.str("");
		if(get_project_path() != "")
			cmd << "cd " << get_project_path() << ";";
		cmd << "echo 'select value from measurements where key = \"visited_" + cov + "s\";' | sqlite3 " << tmp_file("database.db");



		FILE *fp;
		stringstream command;
		char ret[SIZE_STR];
		vector<string> ret_vector;

		fp = popen(cmd.str().c_str(), "r");

		while (fgets(ret,SIZE_STR, fp) != NULL)
			ret_vector.push_back(ret);

		pclose(fp);

		if(!ret_vector.size()){
			printf("No coverage measurements\n");
			exit(0);
		}
		//assert( ret_vector.size() && "No coverage measurements");

		vector<string> tokens = tokenize( *(ret_vector.begin()), " ");

		string coverage_s = tokens[2];

		int archived_coverage = stoi(coverage_s);



		string explanation = cmd_option_str("explanation") + " ";

		while( explanation.length() < 51 )
			explanation = explanation + ".";

		printf("* Coverage of %s", explanation.c_str() );


		if( archived_coverage <  expected_coverage ) printf("\e[31m Less coverage than expected :( (%d < %d)\e[0m\n", archived_coverage, expected_coverage);
		if( archived_coverage >  expected_coverage ) printf("\e[33m More coverage than expected :S (%d > %d)\e[0m\n", archived_coverage, expected_coverage);
		if( archived_coverage == expected_coverage ) printf("\e[32m Same coverage as expected :) (%d)\e[0m\n", archived_coverage);

	}

	end_pass("check_coverage");

}

void gen_final_for_measurement(){

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");
	stringstream cmd;

	make_initial_bc();

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	if(cmd_option_bool("link_bc")){
		// link
		cmd.str("");
		cmd << "llvm-link -o=" << tmp_file("final.bc") << " " << base_path << "/lib/forest.a file-3.bc";
		systm(cmd.str().c_str());

		// from .bc to .s
		cmd.str("");
		cmd << "llc final.bc -o final.s";
		systm(cmd.str().c_str());

		// From .s to .o
		cmd.str("");
		cmd << "gcc -c final.s -o final.o";
		systm(cmd.str().c_str());

		// link
		cmd.str("");
		cmd << "g++ final.o -lpthread -ldl -lrt -o " << output_file;
		systm(cmd.str().c_str());
	} else {
		// From .bc to .s
		cmd.str("");
		cmd << "llc file-3.bc -o file-3.s";
		systm(cmd.str().c_str());

		// from .s to .o
		cmd.str("");
		cmd << "gcc -c file-3.s -o file-3.o";
		systm(cmd.str().c_str());

		// link
		cmd.str("");
		cmd << "g++ file-3.o " << base_path << "/lib/forest.a -lpthread -ldl -lrt -o " << output_file;
		systm(cmd.str().c_str());
	}


}

