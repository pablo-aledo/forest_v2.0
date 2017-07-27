/*
 * =====================================================================================
 * /
 * |     Filename:  stdlibs_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/12/2013 12:41:42 PM
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

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;


map<string, string> options;


int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

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


void read_options(){

	FILE *file = fopen ( tmp_file("options").c_str(), "r" );
	char line_c [ 1024 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line_c, sizeof(line_c), file ) != NULL ){
		line_c[strlen(line_c)-1] = 0;
		string line = string(line_c);
		vector<string> tokens = tokenize(line, " ");

		string key = tokens[0];
		string value = line.substr(key.size()+1);
		options[ tokens[0] ] = value;
		//options[ tokens[0] ] = tokens[1];

		//string value;
		//for ( unsigned int i = 1; i < tokens.size(); i++) {
			//value += tokens[i];
			//value += " ";
		//}

		//options[ tokens[0] ] = value;

		
		
	}
	fclose ( file );
}

bool cmd_option_bool(string key){
	return options[key] == "true";
}

vector<string> cmd_option_vector_str(string key){

	//printf("cmd_option_vector_str %s\n", options[key].c_str());

	vector<string> tokens = tokenize(options[key], "@");
	return tokens;
}


string cmd_option_str(string key){
	return options[key];
}

int cmd_option_int(string key){
	return stoi(options[key]);
}



struct ListFunctions: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ListFunctions() : ModulePass(ID) {}




	virtual bool runOnModule(Module &M) {

		read_options();
		string base_path = cmd_option_str("base_path");
		string list_of_functions = base_path + "/stdlibs/list";
		string list_of_globals = base_path + "/stdlibs/list2";

		set<string> functions_s;
		set<string> globals_s;

		mod_iterator(M, fn){
			string fn_name = fn->getName().str();
			if(fn->begin() != fn->end())
				functions_s.insert(fn_name);
		}

		glo_iterator(M, gl){
			string gl_name = gl->getName().str();
			globals_s.insert(gl_name);
		}

		{
			FILE* file = fopen(list_of_functions.c_str(), "a");
			for( set<string>::iterator it = functions_s.begin(); it != functions_s.end(); it++ ){
				fprintf(file, "%s\n", it->c_str());
			}
			fclose(file);
		}
//		{
//			FILE* file = fopen(list_of_globals.c_str(), "a");
//			for( set<string>::iterator it = globals_s.begin(); it != globals_s.end(); it++ ){
//				fprintf(file, "%s\n", it->c_str());
//			}
//			fclose(file);
//		}
		

		return false;
	}
};



char ListFunctions::ID = 0;
static RegisterPass<ListFunctions> ListFunctions(   "stdlibs_list_functions"  , "List functions" );


