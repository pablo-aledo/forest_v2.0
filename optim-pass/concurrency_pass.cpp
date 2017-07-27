/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2013 09:52:03 AM
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

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;

string operandname( Value* operand );

string itos(int n){
	stringstream ss; ss << n;
	return ss.str();
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


void read_options(){

	FILE *file = fopen ( tmp_file("options").c_str(), "r" );
	char line_c [ 128 ]; /* or other suitable maximum line size */
	
	while ( fgets ( line_c, sizeof(line_c), file ) != NULL ){
		line_c[strlen(line_c)-1] = 0;
		string line = string(line_c);
		vector<string> tokens = tokenize(line, " ");
		options[ tokens[0] ] = tokens[1];
		
	}
	fclose ( file );
}

bool cmd_option_bool(string key){
	return options[key] == "true";
}


string cmd_option_str(string key){
	return options[key];
}



GlobalVariable* make_global_str(Module& M, string name){

	uint64_t length = (uint64_t) name.length()+1;
	//cerr << "---------------------" << name << "---------" << length << endl;
	ArrayType* ArrayTy_0 = ArrayType::get(IntegerType::get(M.getContext(), 8), length );

	GlobalVariable* gvar_array_a = new GlobalVariable(/*Module=*/M,
			/*Type=*/ArrayTy_0,
			/*isConstant=*/false,
			/*Linkage=*/GlobalValue::ExternalLinkage,
			/*Initializer=*/0, // has initializer, specified below
			/*Name=*/"a");

	Constant* const_array_2 = ConstantArray::get(M.getContext(), name.c_str(), true);

	// Global Variable Definitions
	gvar_array_a->setInitializer(const_array_2);

	return gvar_array_a;

}

Constant* pointerToArray( Module& M, GlobalVariable* global_var ){
	ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
	std::vector<Constant*> const_ptr_9_indices;
	const_ptr_9_indices.push_back(const_int64_10);
	const_ptr_9_indices.push_back(const_int64_10);

	Constant* const_ptr_9 = ConstantExpr::getGetElementPtr(global_var, &const_ptr_9_indices[0], const_ptr_9_indices.size());
	return const_ptr_9;
}

struct SeparateSync: public ModulePass {

	static char ID;
	SeparateSync() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fun){
			int n_sync = -1;
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					n_sync++;

					if( in == bb->begin() ){
						bb->setName(fun->getName().str() + "_sync_" + itos(n_sync));
						BasicBlock::iterator it_split = bb->begin(); it_split++;
						bb->splitBasicBlock(it_split);
						break;
					} else {
						BasicBlock::iterator it_split = in;
						bb->splitBasicBlock(it_split, fun->getName().str() + "" + itos(n_sync));
						break;
					}
				}

			}


		}}}


		return false;
	}
};

struct ChangePthreadCJ: public ModulePass {

	static char ID;
	ChangePthreadCJ() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){

					Value* id  = in_c->getArgOperand(0);
					Value* fnc = in_c->getArgOperand(2);

					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								"thread_create" ,
								Type::getVoidTy( M.getContext() ),
								id->getType(),
								fnc->getType(),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(id);
					params.push_back(fnc);
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

				}

				if( fnname == "pthread_join" ){

					Value* id  = in_c->getArgOperand(0);

					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								"thread_join" ,
								Type::getVoidTy( M.getContext() ),
								id->getType(),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(id);
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

				}

			}
		}}}

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" || fnname == "pthread_join" ){
					instr_to_rm.push_back(in_c);
				}



			}


		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		


		return false;
	}
};

struct ChangePthreadC: public ModulePass {

	static char ID;
	ChangePthreadC() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){

					Function* fnc = cast<Function>(in_c->getArgOperand(2));
					Value* arg = in_c->getArgOperand(3);
					
					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(arg);
					CallInst::Create(fnc, params.begin(), params.end(), "", insertpos);
					
					
					
					

				}
			}
		}}}

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){
					instr_to_rm.push_back(in_c);
				}



			}


		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		


		return false;
	}
};

struct ChangeSync: public ModulePass {

	static char ID;
	ChangeSync() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){


				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					instr_to_rm.push_back(in);
					//in_c->dump();
					
					string mutexname = in_c->getArgOperand(0)->getName().str();
					string syncname  = bb->getName().str();

					GlobalVariable* c1 = make_global_str(M, mutexname);
					GlobalVariable* c2 = make_global_str(M, syncname);


					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								fnname == "pthread_mutex_lock"?"mutex_lock":"mutex_unlock" ,
								Type::getVoidTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					params.push_back(pointerToArray(M,c2));
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);


				}

			}


		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}


		return false;
	}
};


struct ChangeSync2: public ModulePass {

	static char ID;
	ChangeSync2() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){


				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_mutex_lock" || fnname == "pthread_mutex_unlock"){

					instr_to_rm.push_back(in);
					//in_c->dump();
					
					string mutexname = operandname(in_c->getArgOperand(0));
					string syncname  = bb->getName().str();

					GlobalVariable* c1 = make_global_str(M, mutexname);
					//GlobalVariable* c2 = make_global_str(M, syncname);


					Value* InitFn = cast<Value> ( M.getOrInsertFunction(
								fnname == "pthread_mutex_lock"?"mutex_lock_2":"mutex_unlock_2" ,
								Type::getVoidTy( M.getContext() ),
								Type::getInt8PtrTy( M.getContext() ),
								//Type::getInt8PtrTy( M.getContext() ),
								(Type *)0
								));


					BasicBlock::iterator insertpos = in; insertpos++;

					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
					//params.push_back(pointerToArray(M,c2));
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);


				}

			}


		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}


		return false;
	}
};



struct RmJoin: public ModulePass {

	static char ID;
	RmJoin() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){


				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_join"){
					instr_to_rm.push_back(in);
				}

			}


		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}


		return false;
	}
};


struct ExtractFn: public ModulePass {

	static char ID;
	ExtractFn() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		read_options();

		//string seed = "_Z3fn1Pv";
		string seed = cmd_option_str("seedfn");

		Function* fnseed = M.getFunction(seed);

		Function::arg_iterator arg_begin = fnseed->arg_begin();
		Function::arg_iterator arg_end   = fnseed->arg_end();
		vector<string> argNames;
		vector<const Type*>   argTypes;
		for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){
			argNames.push_back(it->getName().str());
			const Type* t = it->getType();
			argTypes.push_back(t);
		}

		M.getFunction("main")->eraseFromParent();
		
		Function* func_main = cast<Function> ( M.getOrInsertFunction( "main" ,
					Type::getVoidTy( M.getContext() ),
					(Type *)0
					));

		BasicBlock* entry = BasicBlock::Create(M.getContext(), "entry",func_main,0);

		std::vector<Value*> params;
		for ( unsigned int i = 0; i < argNames.size(); i++) {
			string name = argNames[i];
			const Type* type = argTypes[i];

			AllocaInst* ai = new AllocaInst(type, 0, name.c_str(), entry );
			LoadInst* ai_ptr = new LoadInst(ai,"",entry);

			params.push_back(ai_ptr);

		}

		CallInst::Create(fnseed, params.begin(), params.end(), "", entry);

		ReturnInst::Create(M.getContext(), entry);

		return false;
	}
};

struct BeginConcurrency: public ModulePass {

	static char ID;
	BeginConcurrency() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {


		BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();

		Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_concurrency" ,
					Type::getVoidTy( M.getContext() ),
					(Type *)0
					));

		std::vector<Value*> params;
		CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

		return false;

	}
};

struct BeginEnd: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BeginEnd() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		{
			BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_concurrency" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
		}

		{
			Function::iterator insertpos_f = M.getFunction("main")->end();
			insertpos_f--;
			BasicBlock::iterator insertpos_b = insertpos_f->end();
			insertpos_b--;

	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "end_concurrency" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos_b);
		}

		return false;
	}
};

struct RmCalls: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmCalls() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if( fnname == "pthread_create" ){
					Function* fnc = cast<Function>(in_c->getArgOperand(2));

					if( fnc->getName() != cmd_option_str("seq_name"))
						instr_to_rm.push_back(in_c);
				}
			}
		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		
		return false;
	}
};


struct Secuencialize: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	Secuencialize() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		read_options();
		
		{SeparateSync     pass;   pass.runOnModule(M);}
		{RmCalls          pass;   pass.runOnModule(M);}
		{ChangePthreadC   pass;   pass.runOnModule(M);}
		{ChangeSync       pass;   pass.runOnModule(M);}
		{RmJoin           pass;   pass.runOnModule(M);}

		return false;
	}
};

string floatvalue( ConstantFP * CF ){

	stringstream ret_ss;
	ret_ss.setf( std::ios::fixed, std:: ios::floatfield );
	ret_ss.precision(5);

	if( CF->getType()->getTypeID() == 1)
		ret_ss << CF->getValueAPF().convertToFloat();
	else
		ret_ss << CF->getValueAPF().convertToDouble();

	return ret_ss.str();

}

string operandname( Value* operand ){

	if( ConstantInt::classof(operand) ){
		ConstantInt* CI = dyn_cast<ConstantInt>(operand);
		int64_t val = CI->getSExtValue();
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << val;
		return nameop1_ss.str();
	} else if( ConstantFP::classof(operand) ){
		ConstantFP* CF = dyn_cast<ConstantFP>(operand);

		stringstream nameop1_ss;
		nameop1_ss << "constant" UNDERSCORE << floatvalue(CF);

		return nameop1_ss.str();
	} else if ( ConstantPointerNull::classof(operand) ){
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE "0";
		return nameop1_ss.str();
	} else if(GlobalVariable::classof(operand)){
		return "global" UNDERSCORE + operand->getName().str();
	} else {
		return "register" UNDERSCORE + operand->getName().str();
	}

}


struct LoadStore: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	LoadStore() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( LoadInst::classof(in) ){

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "load_instr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}

					if( StoreInst::classof(in) ){

						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );

						GlobalVariable* c1 = make_global_str(M, nameop1);
						GlobalVariable* c2 = make_global_str(M, nameop2);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "store_instr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
			}
		}

		return false;
	}
};

struct GetConcurrentFunctions: public ModulePass {

	static char ID;
	GetConcurrentFunctions() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		set<string> fn_names;

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);
				
				string fnname = in_c->getCalledFunction()->getName().str();
				if(fnname == "pthread_create" ){

					//in_c->dump();
					Value* arg = in_c->getArgOperand(2);
					//Function* arg_f = cast<Function> arg;
					fn_names.insert(arg->getName().str());
					//cerr << arg->getName().str() << endl;



				}

			}


		}}}

		FILE* file = fopen("concurrent_functions", "w");
		for( set<string>::iterator it = fn_names.begin(); it != fn_names.end(); it++ ){
			fprintf(file, "%s\n", it->c_str());
		}
		fclose(file);

		return false;
	}
};





struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		read_options();
		//cerr << "Option HW " << cmd_option_bool("hello_world") << endl;

		{SeparateSync     pass;   pass.runOnModule(M);}
		//{ChangePthreadC   pass;   pass.runOnModule(M);}
		{ChangeSync       pass;   pass.runOnModule(M);}
		//{LoadStore        pass;   pass.runOnModule(M);}
		//{RmJoin           pass;   pass.runOnModule(M);}
		{ExtractFn        pass;   pass.runOnModule(M);}
		//{BeginConcurrency pass;   pass.runOnModule(M);}
		{BeginEnd         pass;   pass.runOnModule(M);}

		return false;
	}
};


char SeparateSync::ID = 0;
static RegisterPass<SeparateSync> SeparateSync( "conc_sep", "Separate Concurrent accesses" );

char ChangePthreadC::ID = 0;
static RegisterPass<ChangePthreadC> ChangePthreadC( "conc_pthread_c", "Annotate pthread_create calls");

char ChangePthreadCJ::ID = 0;
static RegisterPass<ChangePthreadCJ> ChangePthreadCJ( "conc_pthread_cj", "Annotate pthread_create calls");

char All::ID = 0;
static RegisterPass<All> All( "conc_all", "change calls to pthread_create");

char ChangeSync::ID = 0;
static RegisterPass<ChangeSync> ChangeSync( "conc_changesync", "change calls to mutex get/lock");

char ChangeSync2::ID = 0;
static RegisterPass<ChangeSync2> ChangeSync2( "conc_changesync_2", "change calls to mutex get/lock");

char RmJoin::ID = 0;
static RegisterPass<RmJoin> RmJoin( "conc_rmjoin", "remove pthread_join");

char ExtractFn::ID = 0;
static RegisterPass<ExtractFn> ExtractFn( "conc_extractfn", "Extract a function and its dependencies");

char BeginConcurrency::ID = 0;
static RegisterPass<BeginConcurrency> BeginConcurrency( "begin_concurrency_delme", "Insert the function to begin concurrency analysis");

char BeginEnd::ID = 0;
static RegisterPass<BeginEnd> BeginEnd( "begin_concurrency", "Insert the function to begin concurrency analysis");

char RmCalls::ID = 0;
static RegisterPass<RmCalls> RmCalls( "rm_calls", "remove non-wanted thread creations");

char Secuencialize::ID = 0;
static RegisterPass<Secuencialize> Secuencialize( "secuencialize", "Secuentialize a call to seq_name");

char LoadStore::ID = 0;
static RegisterPass<LoadStore> LoadStore( "loadstore", "annotate load and stores");

char GetConcurrentFunctions::ID = 0;
static RegisterPass<GetConcurrentFunctions> GetConcurrentFunctions( "get_concurrent", "list all concurrent functions");

