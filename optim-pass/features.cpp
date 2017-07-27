/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/29/2014 01:19:20 PM
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

#define SIZE_STR 1024

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;


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

struct IsRecursive: public ModulePass {

	static char ID;
	IsRecursive() : ModulePass(ID) {}

	bool is_recursive(Module &M){

		set<pair<string, string> > calls; // caller, callee

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){
			if(CallInst::classof(in)){
				CallInst* in_c = cast<CallInst>(in);

				string caller_name = fun->getName().str();
				string callee_name;

				if(in_c->getCalledFunction()){
					if(in_c->getCalledFunction()->hasName()){
						callee_name = in_c->getCalledFunction()->getName().str();
					} else {
						callee_name = "";
					}
				} else {
					Value* callee = in_c->getOperand(0);
					if(callee){
						if(callee->hasName()){
							callee_name = callee->getName().str();
						} else {
							ConstantExpr* callee_ci = dyn_cast<ConstantExpr>(callee);
							if(callee_ci){
								if(callee_ci->getOperand(0)->hasName()) callee_name = callee_ci->getOperand(0)->getName().str();
								else callee_name = "";
							} else {

								callee_name = "";
							}
						}
					} else {
						callee_name = "";
					}
				}


				//cerr << "caller " << caller_name << " callee " << callee_name << endl;

				if(callee_name != "")
					calls.insert(pair<string, string>(caller_name, callee_name));
			}
		}}}


		if(!calls.size()) return false;

		for( set<pair<string, string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
			if(it->first == it->second) return true;
		}


		FILE* file = fopen(tmp_file("call_graph").c_str(), "w");
		for( set<pair<string, string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
			fprintf(file, "%s %s\n", it->first.c_str(), it->second.c_str() );
		}
		fclose(file);

		stringstream command;
		command << "tsort " << tmp_file("call_graph") << " 2>&1 > " << tmp_file("tsort_out");

		file = fopen ( tmp_file("tsort_out").c_str(), "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			if(strstr(line, "loop")) return true;
		}
		fclose ( file );
		
		
		return false;
	}


	virtual bool runOnModule(Module &M) {

		FILE* file = fopen(tmp_file("recursive").c_str(), "w");
		fprintf(file, "0\n");
		fclose(file);

		int is_rec = is_recursive(M);

		file = fopen(tmp_file("recursive").c_str(), "w");
		fprintf(file, "%d\n", is_rec);
		fclose(file);

		return false;
	}
};

char IsRecursive::ID = 0;
static RegisterPass<IsRecursive> IsRecursive( "isrecursive", "Finds if a program is recursive");

