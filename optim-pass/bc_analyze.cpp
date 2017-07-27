/*
 * =====================================================================================
 * /
 * |     Filename:  bc_analyze.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/21/2014 06:44:17 AM
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

#include "/media/disk/release/back-end/sqlite3.h"
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Instructions.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/ADT/APFloat.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>


#include <limits>
#include <set>
#include <map>
#include <queue>
#include <string>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;


vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

map<string, string> options;

string tmp_dir(){
	//if(!getenv("TMPDIR")){
		return "/dev/shm/forest";
	//} else {
		//return string(getenv("TMPDIR"));
	//}
}

string tmp_file(string file){
	return tmp_dir() + "/" + file;
}

struct BbAnalyze: public ModulePass {

	static char ID;
	BbAnalyze() : ModulePass(ID) {}

	void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
		size_t pos = 0;
		while((pos = str.find(oldStr, pos)) != std::string::npos){
			str.replace(pos, oldStr.length(), newStr);
			pos += newStr.length();
		}
	}

	string position( string bb_name, string fn_name ){

		myReplace(fn_name, "_", "");

		return fn_name + "_" + bb_name;


	}




	virtual bool runOnModule(Module &M) {

		map<string, int> map_position_to_token;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){

			string fn_name = fun->getName().str(); if(fn_name[0] == '_') fn_name = fn_name.substr(1);
			string bb_name =  bb->getName().str();

			string function_and_bb = position(bb_name, fn_name);

			Instruction* term = bb->getTerminator();
			MDNode* md_node = term->getMetadata((unsigned int)0);
			ConstantInt* ci = cast<ConstantInt>(md_node->getOperand(0));
			int token = ci->getSExtValue();

			map_position_to_token[function_and_bb] = token;

		}}

		FILE* file = fopen(tmp_file("analysis_bc").c_str(), "w");
		for( map<string,int>::iterator it = map_position_to_token.begin(); it != map_position_to_token.end(); it++ ){
			string position = it->first;
			int token = it->second;
			fprintf(file, "%s %d\n", position.c_str(), token);
		}
		fclose(file);
		

		return false;
	}
};


char BbAnalyze::ID = 0;
static RegisterPass<BbAnalyze> BbAnalyze( "bcanalyze", "Relates bb information with source code");

