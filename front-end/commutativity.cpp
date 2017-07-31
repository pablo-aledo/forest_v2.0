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

	stringstream cmd;

	
	cmd << "cp " << prj_file(cmd_option_str("file")) << " file.c; ";
	cmd << "clang -c -emit-llvm file.c;";
	cmd << "opt -mem2reg -simplifycfg -loop-simplify file.bc -o file-canon.bc; ";
	cmd << "opt -load /usr/share/icsa-dswp/lib/libdswp.so -load /usr/share/terrace/lib/libLLVMTerracePass.so -terrace file-canon.bc -o file-te.bc";

	systm(cmd.str().c_str());
}
