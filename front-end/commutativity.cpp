/*
 * =====================================================================================
 * /
 * |     Filename:  commutativity.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/31/2017 09:36:50 AM
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

#include "commutativity.h"

void commutativity_testing(){

	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	stringstream cmd;

	
	cmd << "cp " << prj_file(cmd_option_str("file")) << " file.c; ";
	cmd << "clang -c -emit-llvm file.c;";
	cmd << "opt -mem2reg -simplifycfg -loop-simplify file.bc -o file-canon.bc; ";
	cmd << "opt -load /usr/share/icsa-dswp/lib/libdswp.so -load /usr/share/terrace/lib/libLLVMTerracePass.so -terrace file-canon.bc -o file-te.bc";

	systm(cmd.str().c_str());

	cmd_option_set("seed_function_with_pointers", "main_for.body.split");
	options_to_file();

	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Debug+Asserts/lib/ForestInstr.so -isolate_function_with_pointers < file-te.bc > file-2.bc";
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "mv file-2.bc file.bc";
	systm(cmd.str().c_str());

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Debug+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Debug+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	end_pass("make_bc");

	final();
	run();

}
