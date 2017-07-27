/*
 * =====================================================================================
 * /
 * |     Filename:  concurrent.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/27/2015 02:26:56 PM
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

#include "concurrent.h"
#include "pass_handler.h"
#include <stdio.h>
#include <sstream>

void get_concurrent_functions(){

	
	make_initial_bc();

	stringstream cmd;

	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_pthread_cj < file.bc > file-2.bc";
	systm(cmd.str().c_str());
	cmd.str("");

	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());
	cmd.str("");


	// From .bc to .s
	cmd.str("");
	cmd << "llc file-3.bc -o file-3.s";
	systm(cmd.str().c_str());

	// From .s to .o
	cmd.str("");
	cmd << "gcc -c file-3.s -o file-3.o";
	systm(cmd.str().c_str());

	// link
	cmd.str("");
	cmd << "g++ file-3.o " << base_path << "/lib/forest.a" << " -lpthread -ldl -lrt -o " << output_file;
	systm(cmd.str().c_str());




	dump_forced_free_vars();
	dump_forced_free_hints();


	// Execute resulting file
	cmd.str("");
	cmd << "./" << output_file;


	systm(cmd.str().c_str());



	ifstream input(tmp_file("concurrent_functions").c_str());
	string line;
	
	while( getline( input, line ) ) {
		cout << line << endl;
	}
	

}
