/*
 * =====================================================================================
 * /
 * |     Filename:  optimization_pass.cpp
 * |
 * |  Description:
 * |
 * |      Version:  1.0
 * |      Created:  05/15/2013 05:27:39 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ♪♪  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#define LLVM29


#ifdef LLVM29
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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>
#include "/media/disk/release/back-end/architecture.cpp"
#else
#include <llvm/Pass.h>
#include <llvm/PassManager.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/IR/Operator.h>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>
#include <set>
#include "/home/luis/CurroUC/vippe/hw_llvm/trunk/back-end/architecture.cpp"
#endif


#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;

// Function declaration

int sizeofstruct(const Type* t);
int get_size( const Type* t );
string get_type_str( const Type* t);
string get_flattened_types(const Type* t);

// Type declarations

typedef struct VarInit {
	string name;
	string type;
	string initialization;
} VarInit;

// Helper Functions


	int stoi(string str){
		int ret;
		sscanf(str.c_str(), "%d", &ret);
		return ret;
	}


map<string, string> options;

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


void read_options(){

	ifstream input(tmp_file("options").c_str());
	string line;
	
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, " ");

		string key = tokens[0];
		string value = line.substr(key.size()+1);
		options[ tokens[0] ] = value;
	}

}

bool cmd_option_bool(string key){
	return options[key] == "true";
}

vector<string> cmd_option_vector_str(string key){

	//printf("cmd_option_vector_str %s\n", options[key].c_str());

	vector<string> tokens = tokenize(options[key], "@");
	return tokens;
}

string cmd_option_str(string option){
	if(options[option] == "" ) return "";
	vector<string> tokens = tokenize(options[option].c_str(),"@" );
	string ret = tokens[tokens.size()-1];
	return ret;
}

int cmd_option_int(string key){
	return stoi(options[key]);
}


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

float floatvalue_fl( ConstantFP * CF ){

	if( CF->getType()->getTypeID() == 1)
		return CF->getValueAPF().convertToFloat();
	else
		return CF->getValueAPF().convertToDouble();

}

string operandname( Value* operand ){

	if( ConstantInt::classof(operand) ){
		ConstantInt* CI = dyn_cast<ConstantInt>(operand);
		int64_t val = CI->getSExtValue();
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << get_type_str(operand->getType()) << UNDERSCORE << val;
		
		if( get_type_str(operand->getType()) == "IntegerTyID1" ){
			nameop1_ss.str("");
			if(val == -1)
				nameop1_ss << "constant_bool_true";
			else
				nameop1_ss << "constant_bool_false";
		}

		return nameop1_ss.str();
	} else if( ConstantFP::classof(operand) ){
		ConstantFP* CF = dyn_cast<ConstantFP>(operand);
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << get_type_str(operand->getType()) << UNDERSCORE << floatvalue(CF);
		return nameop1_ss.str();
	} else if ( ConstantPointerNull::classof(operand) ){
		string type = get_type_str(operand->getType());
		stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << 0;
		return nameop1_ss.str();
	} else if(GlobalVariable::classof(operand)){
		return "global" UNDERSCORE + operand->getName().str();
	} else if(Function::classof(operand)){
		string name = operand->getName();
		if(name.substr(0,1) == "_") name = name.substr(1);
		return "function" UNDERSCORE + name;
	} else {
		return "register" UNDERSCORE + operand->getName().str();
	}

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

	#ifdef LLVM29
	Constant* const_array_2 = ConstantArray::get(M.getContext(), name.c_str(), true);
	#else
	Constant* const_array_2 = ConstantDataArray::getString(M.getContext(), name.c_str(), true);
	#endif

	// Global Variable Definitions
	gvar_array_a->setInitializer(const_array_2);

	return gvar_array_a;

}

Constant* pointerToArray( Module& M, GlobalVariable* global_var ){
	ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
	std::vector<Constant*> const_ptr_9_indices;
	const_ptr_9_indices.push_back(const_int64_10);
	const_ptr_9_indices.push_back(const_int64_10);

	#ifdef LLVM29
	Constant* const_ptr_9 = ConstantExpr::getGetElementPtr(global_var, &const_ptr_9_indices[0], const_ptr_9_indices.size());
	#else
	Constant* const_ptr_9 = ConstantExpr::getGetElementPtr(global_var, const_ptr_9_indices);
	#endif
	return const_ptr_9;
}

string get_flattened_types(const Type* t){
	//t->dump();

	string ret;
	const StructType* t_struct = dyn_cast<StructType>(t);
	const ArrayType*  t_array  = dyn_cast<ArrayType>(t);
	const SequentialType*  t_sequential  = dyn_cast<SequentialType>(t);

	if(t_struct){
		unsigned int numelems = t_struct->getNumElements();

		for ( unsigned int i = 0; i < numelems; i++) {
			ret += get_flattened_types(t_struct->getElementType(i));
		}

		return ret;
	} else if(t_array){
		unsigned int numelems = t_array->getNumElements();

		for ( unsigned int i = 0; i < numelems; i++) {
			ret += get_flattened_types(t_sequential->getElementType());
		}

		return ret;
		
		
	} else {
		return get_type_str(t) + ",";
	}


}

string get_type_str( const Type* t){

	int typId = t->getTypeID();

	//t->dump();
	//cerr << typId << endl;


	if(typId == 1){
		stringstream name;
		name << "FloatTyID";
		return name.str();
	}

	if(typId == 2){
		stringstream name;
		name << "DoubleTyID";
		return name.str();
	}


	if(typId == 9){
		stringstream name;
		name << "IntegerTyID" << t->getPrimitiveSizeInBits();
		return name.str();
	}

	if(typId == 13){
		return "PointerTyID";
	}

	if(typId == 12){
		return "ArrayTyID";
	}

	if(typId == 0){
		return "VoidTyID";
	}

	if(typId == 11){
		return "StructTyID";
		
		////cerr << "typid 11:";
		////t->dump();
		//const StructType* t_s = cast<StructType>(t);
		//return get_flattened_types(t_s);
		

	}

	t->dump();
	cerr << typId << endl;

	assert(0 && "Unknown Type");

}

string get_op_name_from_id(int opId){

	//cerr << "opID " << opId << endl;

	switch(opId){

		case  8: return "+";
		case  9: return "+";
		case 10: return "-";
		case 11: return "-";
		case 12: return "*";
		case 14: return "/";
		case 13: return "*";
		case 15: return "/";
		case 16: return "/";
		case 17: return "u%";
		case 18: return "%";
		case 19: return "%";
		case 20: return "L";
		case 21: return "R";
		case 22: return "R";
		case 23: return "Y";
		case 24: return "O";
		case 25: return "X";
		default: assert(0 && "Unknown operand");

	}

}

vector<string> get_indexes(GetElementPtrInst* instr){

	vector<string> ret;
	User::op_iterator it_begin = instr->idx_begin();
	User::op_iterator it_end   = instr->idx_end();

	for( User::op_iterator it = it_begin; it != it_end; it++){

		ConstantInt* CI = dyn_cast<ConstantInt>(it->get());
		if(CI){
			int64_t val = CI->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant_PointerTyID_" << val;
			ret.push_back( nameop1_ss.str() );
		} else {
			Value* value = it->get();
			string name = value->getName().str();
			stringstream nameop1_ss; nameop1_ss << "register" UNDERSCORE << name;
			ret.push_back( nameop1_ss.str() );


		}
	}

	return ret;

}


vector<int> get_indexes_gepop(GEPOperator* gepop){

	vector<int> ret;
	User::op_iterator it_begin = gepop->idx_begin();
	User::op_iterator it_end   = gepop->idx_end();

	for( User::op_iterator it = it_begin; it != it_end; it++){

		ConstantInt* CI = dyn_cast<ConstantInt>(it->get());
		if(CI){
			int64_t val = CI->getSExtValue();
			ret.push_back(val);
		} else {

			assert(0 && "non-constant index in gepop");

		}
	}

	return ret;

}



vector<int> get_dimensions( const ArrayType* t ){

		vector<int> dims;
		while(true){
			if( !t ) break;
			dims.push_back(t->getNumElements());
			t = dyn_cast<ArrayType>(t->getElementType());

		};

		return dims;
}

int element_size( const ArrayType* t ){

	const Type* last_type;

	while(true){
		if( !t ) break;
		last_type = t;
		t = dyn_cast<ArrayType>(t->getElementType());
	};

	last_type = dyn_cast<ArrayType>(last_type)->getElementType();

	//return primary_size( last_type );

	const StructType* t_s = dyn_cast<StructType>(last_type);

	if (t_s){
		return sizeofstruct(last_type);
	} else {
		return primary_size(get_type_str(last_type));
	}

}

const Type* element_type( const ArrayType* t ){

	const Type* last_type;

	while(true){
		if( !t ) break;
		last_type = t;
		t = dyn_cast<ArrayType>(t->getElementType());
	};

	last_type = dyn_cast<ArrayType>(last_type)->getElementType();

	return last_type;

}

int product(vector<int> elem){
	int prod = 1;
	for( vector<int>::iterator it = elem.begin(); it != elem.end(); it++ ){
		prod *= *it;
	}
	return prod;
}

int sizeofstruct(const Type* t){

	int ret = 0;
	const StructType* t_s = dyn_cast<StructType>(t);

	unsigned int numelems = t_s->getNumElements();

	for ( unsigned int i = 0; i < numelems; i++) {
		ret += get_size( t_s->getElementType(i) );
	}

	//return t_s->getNumElements();
	return ret;
}

int get_size( const Type* t ){

	const ArrayType* t_a = dyn_cast<ArrayType>(t);
	const StructType* t_s = dyn_cast<StructType>(t);


	if( t_a ){
		return product(get_dimensions(t_a))*element_size(t_a);
	} else if (t_s){
		return sizeofstruct(t);
	} else {
		return primary_size(get_type_str(t));
	}

}

vector<string> get_nested_sizes( const ArrayType* t ){

	//const PointerType* t_p = dyn_cast<PointerType>(t);
	//t = dyn_cast<ArrayType>(t_p->getElementType());

	vector<int> ret;

	const ArrayType* t_ini = t;

	//const ArrayType* t_a = dyn_cast<ArrayType>(t);
	//if( !t_a ){ ret.push_back(1); return ret; }

	//t->dump(); fflush(stderr);
	//cerr << "nestedsizes" << t << endl; fflush(stderr);

	ret.push_back( t->getNumElements() * get_size(t->getElementType()) );

	//cerr << "nestedsizes2" << endl; fflush(stderr);


	while(true){
		t = dyn_cast<ArrayType>(t->getElementType());
		if( !t ) break;
		ret.push_back( t->getNumElements() * get_size(t->getElementType()) );
	};

	ret.push_back( element_size(t_ini) );


	vector<string> ret2;// ret2.push_back("0");
	for( vector<int>::iterator it = ret.begin(); it != ret.end(); it++ ){
		stringstream ss;
		ss << "constant" UNDERSCORE;
		ss << "_IntegerTyID32_" << *it;
		ret2.push_back(ss.str());
	}
	


	return ret2;


}

vector<string> get_struct_offsets( const StructType* t ){

	vector<string> ret;

	unsigned int numelems = t->getNumElements();

	int offset = 0;

	for ( unsigned int i = 0; i < numelems; i++) {
		stringstream ss;
		ss << "constant" UNDERSCORE;
		ss << "_IntegerTyID32_" << offset;
		ret.push_back(ss.str());

		offset += get_size( t->getElementType(i) );
	}

	return ret;

}

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

string itos( int value ){
	stringstream ret_ss;
	ret_ss << value;
	return ret_ss.str();
}

int get_offset(const Type* t, int debug = 1){

	//cerr << "get_offset "; t->dump();
	//const PointerType*      t_pointer      = dyn_cast<PointerType>(t);
	//const StructType*       t_struct       = dyn_cast<StructType>(t);
	const ArrayType*        t_array        = dyn_cast<ArrayType>(t);
	//const SequentialType*   t_sequential   = dyn_cast<SequentialType>(t);
	//const IntegerType*      t_integer      = dyn_cast<IntegerType>(t);
	const CompositeType*    t_composite    = dyn_cast<CompositeType>(t);
#ifndef LLVM29
	CompositeType*          t_composite_2  = (CompositeType*)t_composite;
#endif

	string type_str = get_type_str(t);

	if(type_str == "PointerTyID"){
		//cerr << "pointer " << endl;
		//return get_offset(t_pointer->getElementType());
		return get_size(t);
	} else if( type_str == "StructTyID"){
		return 1;
	} else if(type_str == "ArrayTyID"){
		//cerr << "array " << endl;

		int sum = 0;
		for ( unsigned int i = 0; i < t_array->getNumElements(); i++) {
#ifdef LLVM29
			sum += get_offset(t_composite->getTypeAtIndex(i));
#else
			sum += get_offset(t_composite_2->getTypeAtIndex(i));
#endif
		}

		return sum;
	} else if( type_str == "IntegerTyID"){

		//cerr << "Integer" << endl;

		return get_size(t);

	} else if( type_str == "IntegerTyID64"){
		//cerr << "Integer64" << endl;

		return get_size(t);
	} else if( type_str == "IntegerTyID32"){
		//cerr << "Integer32" << endl;

		return get_size(t);
	} else if( type_str == "IntegerTyID16"){
		//cerr << "Integer16" << endl;

		return get_size(t);

	} else if( type_str == "IntegerTyID8"){
		//cerr << "Integer8" << endl;

		return get_size(t);

	} else if (type_str == "DoubleTyID"){
		//cerr << "double" << endl;

		return get_size(t);

	} else if (type_str == "FloatTyID"){
		//cerr << "float" << endl;

		return get_size(t);

	} else {

		//cerr << "----" << endl;
		//cerr << "otro" << endl;
		//t->dump();
		cerr << type_str << endl;
		assert(0 && "Unknown Type");

	}

}

string get_offset_tree_rec( const Type* t, int* base){

	//const PointerType*      t_pointer      = dyn_cast<PointerType>(t);
	const StructType*       t_struct       = dyn_cast<StructType>(t);
	const ArrayType*        t_array        = dyn_cast<ArrayType>(t);
	//const SequentialType*   t_sequential   = dyn_cast<SequentialType>(t);
	//const IntegerType*      t_integer      = dyn_cast<IntegerType>(t);
	const CompositeType*    t_composite    = dyn_cast<CompositeType>(t);
#ifndef LLVM29
	CompositeType*          t_composite_2  = (CompositeType*) t_composite;
#endif

	string type_str = get_type_str(t);

	if(type_str == "PointerTyID"){
		//cerr << "pointer " << primary_size(t) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";

		(*base) = (*base) + primary_size(get_type_str(t));
		//base += get_offset(t);

		return ret;
	} else if( type_str == "StructTyID"){

		//cerr << "struct" << endl;

		string aux = "(";
		for ( unsigned int i = 0; i < t_struct->getNumElements(); i++) {
			//cerr << "element " << i << endl;
			aux += get_offset_tree_rec(t_struct->getElementType(i),base);
		}
		//aux += "," + itos(get_offset(t));
		aux += ",1";
		aux += ")";


		return aux;

	} else if(type_str == "ArrayTyID"){

		//cerr << "array" << endl;
		//t->dump();

		string aux = "(";
		for ( unsigned int i = 0; i < t_array->getNumElements(); i++) {
#ifdef LLVM29
			aux += get_offset_tree_rec(t_composite->getTypeAtIndex(i),base);
#else
			aux += get_offset_tree_rec(t_composite_2->getTypeAtIndex(i),base);
#endif
		}
		//aux += "," + itos(get_offset(t_array->getElementType()));
		aux += "," + itos(get_offset(t));
		aux += ")";
		return aux;


	} else if( type_str == "IntegerTyID"){

		//cerr << "integer " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;

	} else if( type_str == "IntegerTyID32"){

		//cerr << "integer32 " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;
	} else if( type_str == "IntegerTyID64"){

		//cerr << "integer64 " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;
	} else if( type_str == "IntegerTyID16"){

		//cerr << "integer32 " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;

	} else if( type_str == "IntegerTyID8"){

		//cerr << "integer8 " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;

	} else if (type_str == "DoubleTyID"){

		//cerr << "double " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;

	} else if (type_str == "FloatTyID"){

		//cerr << "float " << primary_size(get_type_str(t)) << endl;
		string ret = "(" + itos(*base) + "," + itos(get_offset(t)) + ")";
		(*base) = (*base) + primary_size(get_type_str(t));
		return ret;

	} else {

		cerr << "----" << endl;
		cerr << "otro" << endl;
		t->dump();
		cerr << type_str << endl;
		assert(0 && "Unknown Type");

	}
}

string get_offset_tree( const Type* t){

	const SequentialType*   t_sequential   = dyn_cast<SequentialType>(t);

	string type_str = get_type_str(t);

	assert( type_str == "PointerTyID" );

	int base = 0;
	return "(" + get_offset_tree_rec(t_sequential->getElementType(), &base) + "," + itos(get_size(t_sequential->getElementType())) + ")";

}


// Optimization passes

struct FillNames : public ModulePass {

	void change_dot_names( Module &M ){

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){
			if(in->hasName()){
				string name = in->getName();
				myReplace(name, ".", "");
				in->setName(name);
			}
		}}}
	}

	void put_operator_names( Module &M ){


		//mod_iterator(M, fun){
			//fun_iterator(fun,bb){
				//blk_iterator(bb, in){

					//string name = in->getName().str();
					//myReplace(name, "_", "");
					//in->setName(name);


				//}
			//}
		//}

		glo_iterator(M,gl){

			string name = gl->getName().str();
			myReplace(name, "_", "");
			gl->setName(name);

		}



		mod_iterator(M, fun){


			Function::arg_iterator arg_begin = fun->arg_begin();
			Function::arg_iterator arg_end   = fun->arg_end();
			for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){
				if(!it->hasName()) it->setName("a");
			}


			fun_iterator(fun,bb){
				blk_iterator(bb, in){

					if( UnaryInstruction::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( BinaryOperator::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->getOperand(1)->hasName() )
							in->getOperand(1)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( CmpInst::classof(in) ){
						if( !in->getOperand(0)->hasName() )
							in->getOperand(0)->setName("r");
						if( !in->getOperand(1)->hasName() )
							in->getOperand(1)->setName("r");
						if( !in->hasName() )
							in->setName("r");
					}

					if( GetElementPtrInst::classof(in) ){
						if( !in->hasName() )
							in->setName("r");
					}

					if( CallInst::classof(in) ){
						if( !in->hasName() )
							if( !(in->getType()->isVoidTy()) )
								in->setName("r");
					}




				}}}

	}


	void put_block_names( Module &M ){

		mod_iterator(M, fun){
			fun_iterator(fun,bb){
				if( !bb->hasName() )
					bb->setName("b");
			} }


	}

	void put_global_names(Module &M){

		glo_iterator(M,gl){


			GlobalVariable*    global_var   = cast<GlobalVariable>(gl);
			if( !global_var->hasName() ) global_var->setName("g");

		}
	}

	static char ID;
	FillNames() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		change_dot_names(M);
		put_operator_names(M);
		put_block_names(M);
		put_global_names(M);
		

		return false;
	}
};

struct FPointerhook: public ModulePass {
	static char ID;
	FPointerhook() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {
		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();

				string fn_name;
				if(!hasname){
					Value* called_v = in_c->getCalledValue();
					if(!ConstantExpr::classof(called_v) ){
						BasicBlock::iterator insertpos = in;

						string register_name = operandname(called_v);

						//in->dump();
						//cerr << "register_name " << register_name << endl;

						//AllocaInst* ai = new AllocaInst(called_v->getType(), 0, "hook", insertpos );
						//ai->dump();

						GlobalVariable* c1 = make_global_str(M, register_name);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "fp_hook" ,
									called_v->getType(),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst* call = CallInst::Create(InitFn, params.begin(), params.end(), "hola", insertpos);
							
						// cerr << "number of operands " << in->getNumOperands() << endl;
						in->setOperand(in->getNumOperands()-1,call);

						
					}
				}
			}
		}}}

		return false;
	};
};

struct IsolateFunction: public ModulePass {
	static char ID;
	IsolateFunction() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		read_options();

		string seed = cmd_option_str("seed_function");

		Function* fnseed = M.getFunction(seed);

		Function::arg_iterator arg_begin = fnseed->arg_begin();
		Function::arg_iterator arg_end   = fnseed->arg_end();
		vector<string> argNames;
		vector<const Type*> argTypes;
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

#ifdef LLVM29
		CallInst::Create(fnseed, params.begin(), params.end(), "", entry);
#else
		CallInst::Create(fnseed, params, "", entry);
#endif

		ReturnInst::Create(M.getContext(), entry);

		return false;
	}
};


struct SelectInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	SelectInstr() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( SelectInst::classof(in) ){

						//in->dump();
						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						string nameop3 = operandname( in->getOperand(2) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, nameop3);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "select_op" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						params.push_back(pointerToArray(M,c3));
						params.push_back(pointerToArray(M,c4));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

					}
				}
			}
		}

		return false;
	}
};


struct FunctionNames: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	FunctionNames() : ModulePass(ID) {}



	set<string> get_standard_functions(){
		read_options();
		string base_path = cmd_option_str("base_path");
		string list_of_functions = base_path + "/stdlibs/list";
		set<string> functions_v;

		//cerr << list_of_functions << endl;
		
		FILE *file = fopen ( list_of_functions.c_str(), "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			functions_v.insert(string(line));
		}
		fclose ( file );

		return functions_v;
	}


	set<string> get_standard_globals(){
		read_options();
		string base_path = cmd_option_str("base_path");
		string list_of_globals = base_path + "/stdlibs/list2";
		set<string> globals_v;

		
		FILE *file = fopen ( list_of_globals.c_str(), "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			globals_v.insert(string(line));
		}
		fclose ( file );

		return globals_v;
	}


	virtual bool runOnModule(Module &M) {

		set<string> functions_v = get_standard_functions();
		mod_iterator(M, fn){
			string fn_name = fn->getName().str();
			if( functions_v.find(fn_name) != functions_v.end() ){
				fn->setName( "uc_" + fn_name );
			}
		}

//		set<string> globals_v   = get_standard_globals();
//		glo_iterator(M,gl){
//			string gl_name = gl->getName().str();
//			if( globals_v.find(gl_name) != globals_v.end() ){
//				gl->setName( "uc_" + gl_name );
//			}
//		}

		return false;
	}
};

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

struct Demangle: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	Demangle() : ModulePass(ID) {}

	string demangle(string fn_name){
		string command = "c++filt " + fn_name + " > " + tmp_file("demangle");

		//int ret = system(command.c_str());

		ifstream input(tmp_file("demangle").c_str());
		string line;
		getline( input, line );

		return tokenize(line, "()")[0];
		
	}


	set<string> get_standard_functions(){
		read_options();
		string base_path = cmd_option_str("base_path");
		string list_of_functions = base_path + "/stdlibs/list_demangle";
		set<string> functions_v;

		//cerr << list_of_functions << endl;
		
		FILE *file = fopen ( list_of_functions.c_str(), "r" );
		char line [ 128 ]; /* or other suitable maximum line size */
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			functions_v.insert(string(line));
		}
		fclose ( file );

		return functions_v;
	}

	virtual bool runOnModule(Module &M) {

		read_options();

		set<string> functions_v = get_standard_functions();

		mod_iterator(M, fn){
			string fn_name = fn->getName().str();
			if( functions_v.find(fn_name) != functions_v.end() ){
				fn->setName(demangle(fn_name));
			}
		}

		return false;
	}
};



struct RmXBool: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmXBool() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		if(cmd_option_bool("svcomp") || cmd_option_bool("goanna_fpr")) return false;

		mod_iterator(M, fn){

			map<string,vector<Instruction*> > to_rm;

			fun_iterator(fn, bb){
				blk_iterator(bb, in){

					BasicBlock::iterator in_1 = in;
					BasicBlock::iterator in_2 = in_1; in_2++;
					BasicBlock::iterator in_3 = in_2; in_3++;
					BasicBlock::iterator in_4 = in_3; in_4++;

					if(in_4 == bb->end()) continue;

					ICmpInst* in_1_c       = dyn_cast<ICmpInst>(in_1);
					BinaryOperator* in_2_c = dyn_cast<BinaryOperator>(in_2);
					CastInst* in_3_c       = dyn_cast<CastInst>(in_3);
					CmpInst* in_4_c        = dyn_cast<CmpInst>(in_4);

					if( (!in_1_c) || (!in_2_c) && (!in_3_c && !in_4_c) ) continue;


					ConstantInt* constant_int_1_v = dyn_cast<ConstantInt>(in_1_c->getOperand(1));
					if(!constant_int_1_v) continue;
					int constant_int_1 = constant_int_1_v->getSExtValue();

					ConstantInt* constant_int_2_v = dyn_cast<ConstantInt>(in_2_c->getOperand(1));
					if(!constant_int_2_v) continue;
					int constant_int_2 = constant_int_2_v->getSExtValue();

						
					ConstantInt* constant_int_4_v = dyn_cast<ConstantInt>(in_4_c->getOperand(1));
					if(!constant_int_4_v) continue;
					int constant_int_4 = constant_int_4_v->getSExtValue();


					if( constant_int_1 != 0 || constant_int_2 != -1 || constant_int_4 != 0 ) continue;

					
					Value* x = in_1_c->getOperand(0);
					ConstantInt* const_int8_5 = ConstantInt::get(M.getContext(), APInt(8, StringRef("0"), 10));
					ICmpInst* int1_8 = new ICmpInst(in_1, ICmpInst::ICMP_EQ,x,const_int8_5, "");

					blk_iterator(bb, in2){
						for ( unsigned int i = 0; i < in2->getNumOperands(); i++) {
							Value* operand = in2->getOperand(i);
							if(operand == in_4)
								in2->setOperand(i, int1_8);
						}
					}

					to_rm[bb->getName().str()].push_back(in_1);
					to_rm[bb->getName().str()].push_back(in_2);
					to_rm[bb->getName().str()].push_back(in_3);
					to_rm[bb->getName().str()].push_back(in_4);

				}


			}

			// cerr << "fnname: " << fn->getName().str() << endl;

			for( map<string,vector<Instruction*> >::iterator it = to_rm.begin(); it != to_rm.end(); it++){

				vector<Instruction*> vin = it->second;
				string bb_s = it->first;

				// cerr << "bb: " << bb_s << endl;

				for( vector<Instruction*>::iterator it2 = vin.end(); it2 != vin.begin(); ){
					it2--;
					(*it2)->eraseFromParent();
				}

			}

		}

		return false;
	}
};

struct RmErrorFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmErrorFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){
				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
				if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "__VERIFIER_error") instr_to_rm.push_back(in);
				}
			}
		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}

		return false;
	}
};


struct RmPutsFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmPutsFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){
				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
				if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "puts") instr_to_rm.push_back(in);
					if(fn_name == "printf") instr_to_rm.push_back(in);
				}
			}
		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			int numuses = (*it)->getNumUses();
			if(!numuses)
				(*it)->eraseFromParent();
		}

		return false;
	}
};


struct RmPthread: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmPthread() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){
				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
				if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "pthread_create") instr_to_rm.push_back(in);
					if(fn_name == "pthread_join") instr_to_rm.push_back(in);
					if(fn_name == "pthread_mutex_init") instr_to_rm.push_back(in);
				}
			}
		}}}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			int numuses = (*it)->getNumUses();
			if(!numuses)
				(*it)->eraseFromParent();
		}

		return false;
	}
};

struct RmIndetFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmIndetFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){

			vector<Instruction*> instr_to_rm;

			fun_iterator(fn, bb){
			blk_iterator(bb, in){
	
				if( CallInst::classof(in) ){
	
					CallInst* in_c = cast<CallInst>(in);
	
					bool hasname = in_c->getCalledFunction();
					string fn_name;
					if(hasname){
						fn_name = in_c->getCalledFunction()->getName().str();
						if(fn_name == "__VERIFIER_nondet_int") instr_to_rm.push_back(in);
						if(fn_name == "__VERIFIER_nondet_char") instr_to_rm.push_back(in);
						if(fn_name == "__VERIFIER_nondet_uint") instr_to_rm.push_back(in);
						if(fn_name == "__VERIFIER_nondet_bool") instr_to_rm.push_back(in);
						if(fn_name == "__VERIFIER_nondet_long") instr_to_rm.push_back(in);
						if(fn_name == "__VERIFIER_nondet_pointer") instr_to_rm.push_back(in);

						if(fn_name == "_Z21__VERIFIER_nondet_intv") instr_to_rm.push_back(in);
					}
				}
	
			}}
	
	
			for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
				Instruction* instr = *it;
	
				AllocaInst* ai = new AllocaInst(instr->getType(), 0, instr->getName().str(), instr);
				ConstantInt* zero = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));
				vector<Value*> indices; indices.push_back(zero);
				GetElementPtrInst* getelement = GetElementPtrInst::Create(ai, indices.begin(),indices.end(), "pointer", instr);
				LoadInst* load = new LoadInst(getelement, "load", false, instr);
				
				fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if(in->getNumOperands() > 0 && in->getOperand(0) == instr) in->setOperand(0, load);
					if(in->getNumOperands() > 1 && in->getOperand(1) == instr) in->setOperand(1, load);
				}}
	
				if(!(*it)->getNumUses()){
					(*it)->eraseFromParent();
				} else {
					const Type* type = (*it)->getType();
					Instruction* allocainst = new AllocaInst(type, 0, "");
					Instruction* loadinst   = new LoadInst(allocainst, "");
					BasicBlock::iterator ii(*it);
					
					allocainst->insertBefore(ii);
					ReplaceInstWithInst((*it)->getParent()->getInstList(), ii, loadinst);
				}
			}
		}

		return false;
	}
};


struct RmAssumeFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmAssumeFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "__VERIFIER_assume") instr_to_rm.push_back(in);
					if(fn_name == "assumption") instr_to_rm.push_back(in);
					if(fn_name == "assume") instr_to_rm.push_back(in);
				}
			}

		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}

		return false;
	}
};

struct RmMemcpyFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmMemcpyFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name.substr(0,11) == "llvm.memcpy") instr_to_rm.push_back(in);
				}
			}

		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}

		return false;
	}
};


struct RmMalloc: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmMalloc() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name.substr(0,9) == "fr_malloc") instr_to_rm.push_back(in);
					if(fn_name.substr(0,9) == "fr_alloca") instr_to_rm.push_back(in);
					if(fn_name.substr(0,7) == "fr_free") instr_to_rm.push_back(in);
				}
			}

		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			//(*it)->eraseFromParent();
			CallInst* in_c = cast<CallInst>(*it);
			bool hasname = in_c->getCalledFunction();
			if(in_c->getCalledFunction() && (
						in_c->getCalledFunction()->getName() == "fr_malloc" ||
						in_c->getCalledFunction()->getName() == "fr_alloca"
						)
			){
				const PointerType* pointertype = cast<PointerType>((*it)->getType());
				const Type*        pointedtype = pointertype->getElementType();

				Instruction* allocainst = new AllocaInst(pointedtype, 0, "");
				BasicBlock::iterator ii(*it);

				ReplaceInstWithInst((*it)->getParent()->getInstList(), ii, allocainst );
			} else {
				(*it)->eraseFromParent();
			}


		}

		return false;
	}
};



struct ChAssumeFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChAssumeFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "__VERIFIER_assume" || fn_name == "assume") {

						instr_to_rm.push_back(in);

						string nameass = operandname( in_c->getArgOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameass);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "assumption" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
			}

		}}}



		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
	

		return false;
	}
};

struct ChAlloc: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChAlloc() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "malloc" ) {

						instr_to_rm.push_back(in);

						string nameass = operandname( in_c->getArgOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameass);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "fr_malloc" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}

					if(fn_name == "free" ) {

						instr_to_rm.push_back(in);

						string nameass = operandname( in_c->getArgOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameass);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "fr_free" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}

					if(fn_name == "alloca" ) {

						instr_to_rm.push_back(in);

						string nameass = operandname( in_c->getArgOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameass);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "fr_alloca" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}



				}
			}

		}}}



		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			if( (*it)->getNumUses() == 0 )
				(*it)->eraseFromParent();
		}


		return false;
	}
};

struct ChAssertFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	ChAssertFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){

			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				bool hasname = in_c->getCalledFunction();
				string fn_name;
			        if(hasname){
					fn_name = in_c->getCalledFunction()->getName().str();
					if(fn_name == "__VERIFIER_assert") {

						instr_to_rm.push_back(in);

						string nameass = operandname( in_c->getArgOperand(0) );

						GlobalVariable* c1 = make_global_str(M, nameass);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "assertion" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));

						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);

					}
				}
			}

		}}}



		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
	

		return false;
	}
};

struct AddAssertFn: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	AddAssertFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		// Calls to assert and existing VERIFIER_assert
		bool calls_to_assert = false;
		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){
				CallInst* in_c = cast<CallInst>(in);
				if( in_c->getCalledFunction() && in_c->getCalledFunction()->getName() == "assert" ){
					calls_to_assert = true;
				}

				if( in_c->getCalledFunction() && in_c->getCalledFunction()->getName() == "__VERIFIER_assert" ){
					calls_to_assert = true;
				}

			}
		}}}

		// cerr << calls_to_assert;

		if(!calls_to_assert) return false;

		if(M.getFunction("__VERIFIER_assert") && calls_to_assert ){
			vector<Instruction*> instr_to_rm;

			mod_iterator(M, fn){
				fun_iterator(fn, bb){
					blk_iterator(bb, in){
						if( CallInst::classof(in) ){
							CallInst* in_c = cast<CallInst>(in);
							if( in_c->getCalledFunction()->getName() == "assert" ){
								instr_to_rm.push_back(in);


								std::vector<Value*> params;
								params.push_back(in_c->getArgOperand(0));
								CallInst::Create(M.getFunction("__VERIFIER_assert"), params.begin(), params.end(), "",in);

							}
						}
					}}}

			for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
				(*it)->eraseFromParent();
			}
		}






		// If VERIFIER_assert function has body, skip this Pass

		if( !M.getFunction("__VERIFIER_assert"))
			return false;

		if( M.getFunction("__VERIFIER_assert")->begin() != M.getFunction("__VERIFIER_assert")->end() )
			return false;

if(M.getFunction("__VERIFIER_assert"))
  M.getFunction("__VERIFIER_assert")->setName("assert_old");



 Module* mod = &M;



 // Type Definitions
 std::vector<const Type*>FuncTy_0_args;
 FuncTy_0_args.push_back(IntegerType::get(mod->getContext(), 32));
 FunctionType* FuncTy_0 = FunctionType::get(
  /*Result=*/Type::getVoidTy(mod->getContext()),
  /*Params=*/FuncTy_0_args,
  /*isVarArg=*/false);
 
 Function* func_assert = Function::Create(
  /*Type=*/FuncTy_0,
  /*Linkage=*/GlobalValue::ExternalLinkage,
  /*Name=*/"__VERIFIER_assert", mod); 

 // Function: assert (func_assert)
 {
  Function::arg_iterator args = func_assert->arg_begin();
  Value* int32_a = args++;
  int32_a->setName("a");
  
  BasicBlock* label_entry = BasicBlock::Create(mod->getContext(), "entry",func_assert,0);
  BasicBlock* label_bb = BasicBlock::Create(mod->getContext(), "OK",func_assert,0);
  BasicBlock* label_bb1 = BasicBlock::Create(mod->getContext(), "ERROR",func_assert,0);
  BasicBlock* label_bb2 = BasicBlock::Create(mod->getContext(), "bb2",func_assert,0);
  BasicBlock* label_return = BasicBlock::Create(mod->getContext(), "return",func_assert,0);
  
  // Block entry (label_entry)
  ConstantInt* const_int32_3 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
  ICmpInst* int1_6 = new ICmpInst(*label_entry, ICmpInst::ICMP_NE, int32_a, const_int32_3, "");
  BranchInst::Create(label_bb, label_bb1, int1_6, label_entry);
  
  // Block bb (label_bb)
  BranchInst::Create(label_bb2, label_bb);
  
  // Block bb1 (label_bb1)
  BranchInst::Create(label_bb2, label_bb1);
  
  // Block bb2 (label_bb2)
  BranchInst::Create(label_return, label_bb2);
  
  // Block return (label_return)
  ReturnInst::Create(mod->getContext(), label_return);
  
 }
 
		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){
				CallInst* in_c = cast<CallInst>(in);
				if(in_c->getCalledFunction()->getName() == "__VERIFIER_assert"
				|| in_c->getCalledFunction()->getName() == "assert" || in_c->getCalledFunction()->getName() == "assert_old"){
					instr_to_rm.push_back(in);


					std::vector<Value*> params;
					params.push_back(in_c->getArgOperand(0));
					CallInst::Create(func_assert, params.begin(), params.end(), "",in);

				}
			}
		}}}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}



		return false;
	}
};

BasicBlock* return_bb(Function* function){
	fun_iterator(function, bb){
	blk_iterator(bb, in){
		if(ReturnInst::classof(in)) return bb;
	}}

	assert(0 && "No return bb");
}


struct RmInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	RmInstr() : ModulePass(ID) {}


	bool is_special_function(Function* fn){

		string fn_name = fn->getName().str();

		if( fn_name == "global_var_init"  ) return true;
		if( fn_name == "ReturnInstr"      ) return true;
		if( fn_name == "CallInstr_post"   ) return true;
		if( fn_name == "CallInstr"        ) return true;
		if( fn_name == "br_instr_incond"  ) return true;
		if( fn_name == "br_instr_cond"    ) return true;
		if( fn_name == "BeginFn"          ) return true;
		if( fn_name == "begin_bb"         ) return true;
		if( fn_name == "end_bb"           ) return true;
		if( fn_name == "alloca_instr"     ) return true;
		if( fn_name == "store_instr"      ) return true;
		if( fn_name == "load_instr"       ) return true;
		if( fn_name == "binary_op"        ) return true;
		if( fn_name == "cast_instruction" ) return true;
		if( fn_name == "cmp_instr"        ) return true;
		if( fn_name == "getelementptr"    ) return true;
		if( fn_name == "Free_fn"          ) return true;
		if( fn_name == "Memcpy"           ) return true;
		if( fn_name == "assumption"       ) return true;
		if( fn_name == "assertion"        ) return true;
		if( fn_name == "fr_malloc"        ) return true;
		if( fn_name == "fr_alloca"        ) return true;
		if( fn_name == "fr_free"          ) return true;
		if( fn_name == "pthread_mutex_lock"        ) return true;
		if( fn_name == "pthread_mutex_unlock"        ) return true;

		return false;

	}

	Constant* get_zero_of_type(const Type* type, Module& M){

		Constant* ret;

		if     ( get_type_str(type) == "IntegerTyID32" ) ret = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));
		else if( get_type_str(type) == "IntegerTyID16" ) ret = ConstantInt::get(M.getContext(), APInt(16, StringRef("0"), 10));
		else if( get_type_str(type) == "IntegerTyID64" ) ret = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
		else if( get_type_str(type) == "IntegerTyID8"  ) ret = ConstantInt::get(M.getContext(), APInt( 8, StringRef("0"), 10));
		else if( get_type_str(type) == "IntegerTyID1"  ) ret = ConstantInt::get(M.getContext(), APInt( 1, StringRef("0"), 10));
		else if( get_type_str(type) == "PointerTyID"   ) ret = ConstantPointerNull::get(cast<PointerType>(type));
		else if( get_type_str(type) == "DoubleTyID"    ) ret = ConstantFP::get(type, 0);
		else { cerr << "type:" << endl; type->dump(); cerr << get_type_str(type) << endl; assert(0 && "Unknown Type"); }


		return ret;

	}

	void callinstr_operands(Module& M){

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( CallInst::classof(in) ){

				CallInst* in_c = cast<CallInst>(in);

				if(is_special_function(in_c->getCalledFunction())) continue;

				//in_c->dump();

				for ( unsigned int i = 0; i < in->getNumOperands()-1; i++) {
					Constant* zero = get_zero_of_type(in->getOperand(i)->getType(), M);
					//cerr << "operand " << i << endl;
					//in->getOperand(i)->dump();
					in->setOperand(i,zero);
				}
			}
		}}}
	}

	void ret_zero(Module& M){

		mod_iterator(M, fn){
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( ReturnInst::classof(in) ){
				//in->dump();
				//in->getOperand(0)->getType()->dump();
				if(in->getNumOperands() > 0 && get_type_str(in->getOperand(0)->getType()) != "VoidTyID"){
					Constant* zero = get_zero_of_type(in->getOperand(0)->getType(), M);
					in->setOperand(0,zero);
				}
			}
		}}}

	}




	void rm_instr(Module& M){

		vector<Instruction*> rm_instr;
		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( BinaryOperator::classof(in)          ) rm_instr.push_back(in);
					if( CmpInst::classof(in)                 ) rm_instr.push_back(in);
					if( LoadInst::classof(in)                ) rm_instr.push_back(in);
					if( StoreInst::classof(in)               ) rm_instr.push_back(in);
					if( AllocaInst::classof(in)              ) rm_instr.push_back(in);
					if( CastInst::classof(in)                ) rm_instr.push_back(in);
					if( GetElementPtrInst::classof(in)       ) rm_instr.push_back(in);




				}
			}
		}

		for( vector<Instruction*>::iterator it = rm_instr.end()-1; it != rm_instr.begin(); it-- ){
			if((*it)->getNumUses() == 0)
				(*it)->eraseFromParent();
		}
		(*rm_instr.begin())->eraseFromParent();
		


	}


	virtual bool runOnModule(Module &M) {

		ret_zero(M);
		callinstr_operands(M);
		rm_instr(M);

		return false;
	}
};


struct BinaryOp: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BinaryOp() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( BinaryOperator::classof(in) ){

						//in->dump();
						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						int nameop     = in->getOpcode();

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, get_op_name_from_id(nameop));


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "binary_op" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						params.push_back(pointerToArray(M,c3));
						params.push_back(pointerToArray(M,c4));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

						//CallInst* ci = CallInst::Create(InitFn, "", insertpos );

					}
				}
			}
		}

		return false;
	}
};

struct CastInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	CastInstr() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CastInst::classof(in) ){

						if( in->getName() == "alloca point" ) continue;

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string type = get_type_str( in->getType() );
						string sext = dyn_cast<SExtInst>(in)?"true":"false";

						//cerr << nameres << " " << nameop1 << endl;

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, type);
						GlobalVariable* c4 = make_global_str(M, sext);


						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "cast_instruction" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						params.push_back(pointerToArray(M,c3));
						params.push_back(pointerToArray(M,c4));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif


					}
				}
			}
		}

		return false;
	}
};

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
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

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
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

					}
				}
			}
		}

		return false;
	}
};

struct SeparateGetElm: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	SeparateGetElm() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( LoadInst::classof(in) ){


						GEPOperator* gepop = dyn_cast<GEPOperator>(in->getOperand(0));

						bool is_gepop;
						is_gepop = dyn_cast<GEPOperator>(in->getOperand(0)) != NULL;
						is_gepop = is_gepop && dyn_cast<GetElementPtrInst>(in->getOperand(0)) == NULL;

						if(is_gepop){

							Value* pointer = gepop->getPointerOperand();
							User::op_iterator idxbegin = gepop->idx_begin();
							User::op_iterator idxend   = gepop->idx_end();
							vector<Value*> indices(idxbegin, idxend);

#ifdef LLVM29
							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
#else
							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices, "pointer", in);
#endif
							in->setOperand(0,getelement);

							//gepop->dump();
							//pointer->dump();
							//(*idxbegin)->dump();


						}

					}

					if( StoreInst::classof(in) ){

						for ( unsigned int i = 0; i < 2; i++) {

							GEPOperator* gepop = dyn_cast<GEPOperator>(in->getOperand(i));

							bool is_gepop;
							is_gepop = dyn_cast<GEPOperator>(in->getOperand(i)) != NULL;
							is_gepop = is_gepop && dyn_cast<GetElementPtrInst>(in->getOperand(i)) == NULL;

							if(is_gepop){
								//in->dump();


								Value* pointer = gepop->getPointerOperand();
								User::op_iterator idxbegin = gepop->idx_begin();
								User::op_iterator idxend   = gepop->idx_end();
								vector<Value*> indices(idxbegin, idxend);

#ifdef LLVM29
								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
#else
								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices, "pointer", in);
#endif

								in->setOperand(i,getelement);


							}
						}

					}

					if( CallInst::classof(in) ){


						CallInst* in_c = cast<CallInst>(in);

						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {

							GEPOperator* gepop = dyn_cast<GEPOperator>(in_c->getArgOperand(i));


							bool is_gepop;
							is_gepop = dyn_cast<GEPOperator>(in->getOperand(i)) != NULL;
							is_gepop = is_gepop && dyn_cast<GetElementPtrInst>(in->getOperand(i)) == NULL;

							if(is_gepop){

								Value* pointer = gepop->getPointerOperand();
								User::op_iterator idxbegin = gepop->idx_begin();
								User::op_iterator idxend   = gepop->idx_end();
								vector<Value*> indices(idxbegin, idxend);
#ifdef LLVM29
								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
#else
								GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices, "pointer", in);
#endif
								in->setOperand(i,getelement);

							}

						}

					}

					if( GetElementPtrInst::classof(in) ){

						GetElementPtrInst* in_g = cast<GetElementPtrInst>(in);

						GEPOperator* gepop = dyn_cast<GEPOperator>(in_g->getPointerOperand());

						bool is_gepop;
						is_gepop = dyn_cast<GEPOperator>(in_g->getPointerOperand()) != NULL;
						is_gepop = is_gepop && dyn_cast<GetElementPtrInst>(in_g->getPointerOperand()) == NULL;

						if(is_gepop){


							Value* pointer = gepop->getPointerOperand();
							User::op_iterator idxbegin = gepop->idx_begin();
							User::op_iterator idxend   = gepop->idx_end();
							vector<Value*> indices(idxbegin, idxend);
#ifdef LLVM29
							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices.begin(),indices.end(), "pointer", in);
#else
							GetElementPtrInst* getelement = GetElementPtrInst::Create(pointer, indices, "pointer", in);
#endif
							in->setOperand(0,getelement);

						}

					}

				}

			}

		}


		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( LoadInst::classof(in) ){

						ConstantExpr* castop = dyn_cast<ConstantExpr>(in->getOperand(0));

						if(castop){

							Value* pointer = castop->getOperand(0);
							CastInst* castinstr = CastInst::Create(Instruction::BitCast, pointer,castop->getType(), "pointer", in);
							in->setOperand(0,castinstr);

						}

					}

					if( StoreInst::classof(in) ){

						for ( unsigned int i = 0; i < 2; i++) {

							ConstantExpr* castop = dyn_cast<ConstantExpr>(in->getOperand(i));

							if(castop){

								Value* pointer = castop->getOperand(0);
								CastInst* castinstr = CastInst::Create(Instruction::BitCast, pointer,castop->getType(), "pointer", in);
								in->setOperand(i,castinstr);


							}
						}

					}

					if( CallInst::classof(in) ){

						CallInst* in_c = cast<CallInst>(in);

						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {

							ConstantExpr* castop = dyn_cast<ConstantExpr>(in_c->getArgOperand(i));


							if(castop){

								Value* pointer = castop->getOperand(0);
								CastInst* castinstr = CastInst::Create(Instruction::BitCast, pointer,castop->getType(), "pointer", in);
								in->setOperand(i,castinstr);

							}

						}

					}

					if( GetElementPtrInst::classof(in) ){

						GetElementPtrInst* in_g = cast<GetElementPtrInst>(in);

						ConstantExpr* castop = dyn_cast<ConstantExpr>(in_g->getPointerOperand());

						if(castop){

							Value* pointer = castop->getOperand(0);
							CastInst* castinstr = CastInst::Create(Instruction::BitCast, pointer,castop->getType(), "pointer", in);
							in->setOperand(0,castinstr);

						}

					}

				}

			}

		}





		return false;
	}
};

struct IcmpInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	IcmpInstr() : ModulePass(ID) {}

	string get_predicate( CmpInst* instr ){
		switch( instr->getPredicate() ){

			case CmpInst::FCMP_FALSE           : return "";
			case CmpInst::FCMP_OEQ             : return "=";
			case CmpInst::FCMP_OGT             : return ">";
			case CmpInst::FCMP_OGE             : return ">=";
			case CmpInst::FCMP_OLT             : return "<";
			case CmpInst::FCMP_OLE             : return "<=";
			case CmpInst::FCMP_ONE             : return "#";
			case CmpInst::FCMP_ORD             : return "";
			case CmpInst::FCMP_UNO             : return "";
			case CmpInst::FCMP_UEQ             : return "=";
			case CmpInst::FCMP_UGT             : return ">";
			case CmpInst::FCMP_UGE             : return ">=";
			case CmpInst::FCMP_ULT             : return "<";
			case CmpInst::FCMP_ULE             : return "<=";
			case CmpInst::FCMP_UNE             : return "#";
			case CmpInst::FCMP_TRUE            : return "";
			case CmpInst::BAD_FCMP_PREDICATE   : return "";
			case CmpInst::ICMP_EQ              : return "=";
			case CmpInst::ICMP_NE              : return "#";
			case CmpInst::ICMP_UGT             : return "u>";
			case CmpInst::ICMP_UGE             : return "u>=";
			case CmpInst::ICMP_ULT             : return "u<";
			case CmpInst::ICMP_ULE             : return "u<=";
			case CmpInst::ICMP_SGT             : return ">";
			case CmpInst::ICMP_SGE             : return ">=";
			case CmpInst::ICMP_SLT             : return "<";
			case CmpInst::ICMP_SLE             : return "<=";
			case CmpInst::BAD_ICMP_PREDICATE   : return "";
			default: assert(0 && "Unknown Operation");

		}

		return "";
	}

	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CmpInst::classof(in) ){

						string nameres = "register" UNDERSCORE + in->getName().str();
						string nameop1 = operandname( in->getOperand(0) );
						string nameop2 = operandname( in->getOperand(1) );
						string cmptype = get_predicate( cast<CmpInst>(in) );

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, nameop2);
						GlobalVariable* c4 = make_global_str(M, cmptype);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "cmp_instr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						params.push_back(pointerToArray(M,c3));
						params.push_back(pointerToArray(M,c4));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

					}
				}
			}
		}

		return false;
	}
};


struct SwitchInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	SwitchInstr() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		vector<Instruction*> to_rm;

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( SwitchInst::classof(in) ){

						SwitchInst* in_s = cast<SwitchInst>(in);
						BasicBlock* def = cast<BasicBlock>(in_s->getOperand(1));




						to_rm.push_back(in);

						Value* reg = in_s->getOperand(0);

						vector<BasicBlock*> bb_orig_v;
						vector<BasicBlock*> bb_created_v;
						vector<Value*> values_v;
						for ( unsigned int i = 0; i < (in_s->getNumOperands()-2)/2;i++) {
							BasicBlock* bb_orig    = cast<BasicBlock>(in_s->getOperand(2*i+3));
							Value*      value      = in_s->getOperand(2*i+2);
							BasicBlock* bb_created = BasicBlock::Create(M.getContext(), "bb_sw", fn,0);

							bb_orig_v.push_back(bb_orig);
							bb_created_v.push_back(bb_created);
							values_v.push_back(value);
						}

						BranchInst::Create(cast<BasicBlock>(bb_created_v[0]), cast<BasicBlock>(bb));

						for ( unsigned int i = 0; i < bb_orig_v.size(); i++) {
							Instruction* icmp   = new ICmpInst(*(bb_created_v[i]), ICmpInst::ICMP_EQ, reg, values_v[i], "" );
							//BranchInst::Create( bb_orig_v[i], def, icmp, bb_created_v[i]);
							
							if(i==bb_orig_v.size()-1)
								BranchInst::Create( bb_orig_v[i], def, icmp, bb_created_v[i]);
							else
								BranchInst::Create( bb_orig_v[i], bb_created_v[i+1], icmp, bb_created_v[i]);
						}

					}
				}
			}
		}

		for( vector<Instruction*>::iterator it = to_rm.begin(); it != to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}

		return false;
	}
};


struct BrInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	BrInstr() : ModulePass(ID) {}

	vector<string> basic_blocks( Module::iterator fn ){

		vector<string> ret;

		fun_iterator(fn, bb){

			ret.push_back( bb->getName().str() );

		}

		return ret;
	}

	map<string, map<string, bool> > conectivity_matrix( Module::iterator fn ){

		map<string, map<string, bool> > ret;

		vector<string> bbs = basic_blocks( fn );

		for ( unsigned int x = 0; x < bbs.size(); x++) {
			for ( unsigned int y = 0; y < bbs.size(); y++) {
				string src = bbs[x];
				string dst = bbs[y];
				ret[src][dst] = 0;
			}
		}

		fun_iterator(fn, bb){

			BasicBlock::iterator in = bb->end(); in--;

			BranchInst* in_b = dyn_cast<BranchInst>(in);
			if(!in_b) continue;

			for ( unsigned int i = 0; i < in_b->getNumSuccessors(); i++) {
				string src = bb->getName().str();
				string dst = in_b->getSuccessor(i)->getName().str();

				ret[src][dst] = 1;

			}

		}

		return ret;

	}


	set<string> one_pass_reachable(string bb, map<string, map<string, bool> > connectivity, set<string> reachable_set, Module::iterator fn ){


		//cerr << "opr1" << endl; fflush(stderr);
		
		set<string> ret = reachable_set;
		vector<string> bbs = basic_blocks( fn );

		for( set<string>::iterator it = reachable_set.begin(); it != reachable_set.end(); it++ ){

			string src = *it;

			for ( unsigned int i = 0; i < connectivity.size(); i++) {
				string dst = bbs[i];
				if( connectivity[src][dst] ) ret.insert(dst);
			}
		}

		return ret;

	}

	set<string> reachable(string bb, Module::iterator fn ){

		map<string, map<string, bool> > connectivity = conectivity_matrix(fn);

		set<string> reachable_set_last;
		set<string> reachable_set;
		//cerr << "reach1" << endl; fflush(stderr);
		reachable_set.insert(bb);
		//cerr << "reach2" << endl; fflush(stderr);

		while( reachable_set_last != reachable_set ){
			reachable_set_last = reachable_set;
			reachable_set      = one_pass_reachable( bb, connectivity, reachable_set, fn);
		}

		return reachable_set;

	}


	set<string> intersection( set<string> s1, set<string> s2 ){

		set<string> ret;
		for( set<string>::iterator it = s1.begin(); it != s1.end(); it++ ){
			if( s2.find(*it) != s2.end() ) ret.insert(*it);
		}

		return ret;

	}



	virtual bool runOnModule(Module &M) {


		mod_iterator(M, fn){

			map<string, map<string, bool> > conectivity = conectivity_matrix(fn);
			vector<string> bbs = basic_blocks( fn );

			//for( vector<string>::iterator it = bbs.begin(); it != bbs.end(); it++ ){
				//cerr << *it << " ";
			//} cerr << endl;
			

			//for ( unsigned int x = 0; x < bbs.size(); x++) {
				//for ( unsigned int y = 0; y < bbs.size(); y++) {
					//string src = bbs[x];
					//string dst = bbs[y];
					//cerr << conectivity[src][dst];
				//}
				//cerr << endl;
			//}
			//cerr << endl;
			
			//cerr << "\033[32m" << fn->getName().str() << "\033[0m" << endl;

			//for ( unsigned int i = 0; i < bbs.size(); i++) {

				//string src = bbs[i];

				//set<string> reachable_set = reachable( src, fn );

				//cerr << "\033[31m" << src << "\033[0m" << endl;
				//for( set<string>::iterator it = reachable_set.begin(); it != reachable_set.end(); it++ ){
					//cerr << *it << " ";
				//} cerr << endl;

			//}
			

			//for( map<string,map<string, bool> >::iterator it = conectivity.begin(); it != conectivity.end(); it++ ){
				//for( map<string,bool>::iterator it2 = it->second.begin(); it2 != it->second.end(); it2++ ){

					//cerr << " " << it2->second << " ";
					
				//}

				//cerr << endl;
				
			//}
			


			fun_iterator(fn, bb){

				blk_iterator(bb, in){
					if( BranchInst::classof(in) ){

						BranchInst* in_b = cast<BranchInst>(in);

						if( in_b->isConditional() ){

							//string name1 = in_b->getSuccessor(0)->getName().str();
							//string name2 = in_b->getSuccessor(1)->getName().str();
							//set<string> reachable_1 = reachable(name1, fn);
							//set<string> reachable_2 = reachable(name2, fn);

							//in_b->dump();

							//cerr << "Reachable states from true:";
							//for( set<string>::iterator it = reachable_1.begin(); it != reachable_1.end(); it++ ){
								//cerr << (*it) << ", ";
							//}
							//cerr << endl;
							
							//cerr << "Reachable states from false:";
							//for( set<string>::iterator it = reachable_2.begin(); it != reachable_2.end(); it++ ){
								//cerr << (*it) << ", ";
							//}
							//cerr << endl;

							//set<string> joints = intersection(reachable_1, reachable_2);

							//cerr << "Intersection:";
							//for( set<string>::iterator it = joints.begin(); it != joints.end(); it++ ){
								//cerr << (*it) << ", ";
							//}
							//cerr << endl;

							string joints_s;
							//for( set<string>::iterator it = joints.begin(); it != joints.end(); it++ ){
								//joints_s = joints_s + (*it) + ",";
							//}
							

							//cerr << "\033[31m" << joints_s << "\033[0m" << endl;

							string nameop1 = operandname( in->getOperand(0) );

							GlobalVariable* c1 = make_global_str(M, nameop1);
							GlobalVariable* c2 = make_global_str(M, joints_s);

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "br_instr_cond" ,
										Type::getInt1Ty( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; //insertpos++;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c1));
							params.push_back(pointerToArray(M,c2));

#ifdef LLVM29
							CallInst* ci = CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
							CallInst* ci = CallInst::Create(InitFn, params, "", insertpos);
#endif
							
							if( in_b->isConditional() )
								in_b->setCondition(ci);

						} else {

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "br_instr_incond" ,
										Type::getVoidTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in; //insertpos++;

							std::vector<Value*> params;
#ifdef LLVM29
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
							CallInst::Create(InitFn, params, "", insertpos);
#endif

						}
					}
				}
			}
		}

		return false;
	}
};


struct SpecialCall: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	SpecialCall() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CallInst::classof(in) ){

						//cerr << "Instruction ";
						//in->dump();

						CallInst* in_c = cast<CallInst>(in);

						bool hasname = in_c->getCalledFunction();

						string fn_name;
					        if(hasname)
							fn_name = in_c->getCalledFunction()->getName().str();
						else
							fn_name ="";

						if(fn_name == "global_var_init" ) continue;
						if(fn_name == "ReturnInstr" ) continue;
						if(fn_name == "CallInstr_post" ) continue;
						if(fn_name == "CallInstr" ) continue;
						if(fn_name == "pthread_mutex_lock" ) continue;
						if(fn_name == "pthread_mutex_unlock" ) continue;



						if(
						   fn_name != "_Z10force_freePi"   && 
						   fn_name != "_Z9pivot_varPi"
						   )
							continue;



						stringstream operand_list;
						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {
							string name = operandname( in_c->getArgOperand(i) );
							operand_list << name << ",";
						}


						string oplist  = operand_list.str();
						string ret_to = operandname( in_c );
						string ret_type = get_type_str( in_c->getType() );

						bool freefn = (fn_name == "_Z10force_freePi");
						bool forcepivot = (fn_name == "_Z9pivot_varPi");


						if(freefn){

							instr_to_rm.push_back(in);

							
							GlobalVariable* c2 = make_global_str(M, oplist );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "Free_fn" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c2));
#ifdef LLVM29
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
							CallInst::Create(InitFn, params, "", insertpos);
#endif
						} else if(forcepivot) {

							GlobalVariable* c2 = make_global_str(M, oplist );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "pivot_variable" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));

							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c2));
#ifdef LLVM29
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
							CallInst::Create(InitFn, params, "", insertpos);
#endif

						} else {

							assert(0 && "Unknown special function");

						}
							

					}
				}
			}
		}

		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		
		



		return false;
	}
};



struct CallInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	CallInstr() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			map<string, int> call_id;
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CallInst::classof(in) ){

						//cerr << "Instruction ";
						//in->dump();

						CallInst* in_c = cast<CallInst>(in);

						bool hasname = in_c->getCalledFunction();

						string fn_name;
					        if(hasname){
							fn_name = in_c->getCalledFunction()->getName().str();
						} else {

							Value* called_v = in_c->getCalledValue();
							if( ConstantExpr::classof(called_v) ){
								ConstantExpr* called_e = cast<ConstantExpr>(called_v);
								Function* called_f = cast<Function>(called_e->getOperand(0));
								fn_name = called_f->getName().str();
							} else {
								fn_name = operandname(called_v);
							}
							


						}

						if( fn_name == "global_var_init"  ) continue;
						if( fn_name == "_Z10force_freePi" ) continue;
						if( fn_name == "_Z9pivot_varPi"   ) continue;
						if( fn_name == "ReturnInstr"      ) continue;
						if( fn_name == "CallInstr_post"   ) continue;
						if( fn_name == "CallInstr"        ) continue;
						if( fn_name == "end_sim"          ) continue;
						if( fn_name == "pointer_ranges"   ) continue;
						if(fn_name == "assumption"        ) continue;
						if(fn_name == "assume"        ) continue;
						if(fn_name == "__VERIFIER_assume" ) continue;
						if(fn_name == "pthread_mutex_lock" ) continue;
						if(fn_name == "pthread_mutex_unlock" ) continue;
						if(fn_name == "rv_emit_async" ) continue;
						//if(fn_name == "__VERIFIER_assert" ) continue;

						if( fn_name.substr(0,11) == "llvm.memcpy" ) continue;


						stringstream operand_list;
						for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {
							string name = operandname( in_c->getArgOperand(i) );
							operand_list << name << ",";
						}


						string oplist  = operand_list.str();
						string ret_to = operandname( in_c );
						string ret_type = get_type_str( in_c->getType() );
						string call_id_str = itos(call_id[fn_name]++);
						
						//cerr << fn_name << endl;
						//cerr << oplist  << endl;
						//cerr << fn_oplist << endl;
						
						GlobalVariable* c1 = make_global_str(M, fn_name );
						GlobalVariable* c2 = make_global_str(M, oplist );
						GlobalVariable* c3 = make_global_str(M, ret_to );
						GlobalVariable* c4 = make_global_str(M, ret_type );
						GlobalVariable* c5 = make_global_str(M, call_id_str);
						GlobalVariable* c6 = make_global_str(M, fn->getName().str() );

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "CallInstr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						Value* InitFn_post = cast<Value> ( M.getOrInsertFunction( "CallInstr_post" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));



						BasicBlock::iterator insertpos = in;

						std::vector<Value*> params1;
						params1.push_back(pointerToArray(M,c2));
						params1.push_back(pointerToArray(M,c3));
						params1.push_back(pointerToArray(M,c5));
#ifdef LLVM29
						CallInst::Create(InitFn, params1.begin(), params1.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params1, "", insertpos);
#endif

						insertpos++; in++;

						std::vector<Value*> params2;
						params2.push_back(pointerToArray(M,c1));
						params2.push_back(pointerToArray(M,c4));
						params2.push_back(pointerToArray(M,c6));
#ifdef LLVM29
						CallInst::Create(InitFn_post, params2.begin(),params2.end(), "", insertpos);
#else
						CallInst::Create(InitFn_post, params2, "", insertpos);
#endif

						in--;

					}
				}
			}
		}


		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( ReturnInst::classof(in) ){

						ReturnInst* in_r = cast<ReturnInst>(in);


						string returnoperand;
						if( !in_r->getReturnValue() )
							returnoperand = "register" UNDERSCORE;
						else
							returnoperand = operandname( in_r->getReturnValue() );

						GlobalVariable* c1 = make_global_str(M, returnoperand );

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "ReturnInstr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif




					}

				}
			}
		}





		return false;
	}
};


struct Memcpy: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	Memcpy() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		vector<Instruction*> instr_to_rm;

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( CallInst::classof(in) ){

						CallInst* in_c = cast<CallInst>(in);

						bool hasname = in_c->getCalledFunction();

						string fn_name;
					        if(hasname){
							fn_name = in_c->getCalledFunction()->getName().str();
						} else {

							Value* called_v = in_c->getCalledValue();

							if(! ConstantExpr::classof(called_v)) continue;

							ConstantExpr* called_e = cast<ConstantExpr>(called_v);
							Function* called_f = cast<Function>(called_e->getOperand(0));

							fn_name = called_f->getName().str();
							


						}


						if( fn_name.substr(0,11) == "llvm.memcpy" ){

							instr_to_rm.push_back(in);

							stringstream operand_list;
							for ( unsigned int i = 0; i < in_c->getNumOperands()-1; i++) {
								string name = operandname( in_c->getArgOperand(i) );
								operand_list << name << ",";
							}


							string op2;
							//in_c->getArgOperand(1)->dump();
							ConstantExpr* op1_ce = dyn_cast<ConstantExpr>(in_c->getArgOperand(1));
							if(op1_ce){
								//op1_ce->getOperand(0)->dump();
								op2 = "register_" + op1_ce->getOperand(0)->getName().str();
							} else {
								op2 = "register_" + in_c->getArgOperand(1)->getName().str();
							}



							string op1 = operandname( in_c->getArgOperand(0) );
							//string op2 = operandname( in_c->getArgOperand(1) );
							string op3 = operandname( in_c->getArgOperand(2) );
							string op4 = operandname( in_c->getArgOperand(3) );
							string op5 = operandname( in_c->getArgOperand(4) );

							string oplist  = operand_list.str();
							string ret_to = operandname( in_c );
							string ret_type = get_type_str( in_c->getType() );

							//cerr << fn_name << endl;
							//cerr << oplist  << endl;
							//cerr << fn_oplist << endl;


							GlobalVariable* c1 = make_global_str(M, op1 );
							GlobalVariable* c2 = make_global_str(M, op2 );
							GlobalVariable* c3 = make_global_str(M, op3 );
							GlobalVariable* c4 = make_global_str(M, op4 );
							GlobalVariable* c5 = make_global_str(M, op5 );

							Value* InitFn = cast<Value> ( M.getOrInsertFunction( "Memcpy" ,
										Type::getVoidTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										Type::getInt8PtrTy( M.getContext() ),
										(Type *)0
										));


							BasicBlock::iterator insertpos = in;

							std::vector<Value*> params;
							params.push_back(pointerToArray(M,c1));
							params.push_back(pointerToArray(M,c2));
							params.push_back(pointerToArray(M,c3));
							params.push_back(pointerToArray(M,c4));
							params.push_back(pointerToArray(M,c5));
#ifdef LLVM29
							CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
							CallInst::Create(InitFn, params, "", insertpos);
#endif

						}


					}
				}
			}
		}


		for( vector<Instruction*>::iterator it = instr_to_rm.begin(); it != instr_to_rm.end(); it++ ){
			(*it)->eraseFromParent();
		}
		

		return false;
	}
};

struct ExternalFn: public ModulePass {
	static char ID; // Pass identification, replacement for typed
	ExternalFn() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			if(fn->begin() == fn->end() )
				cerr << fn->getName().str() << endl;
		}

		return false;
	}
};


struct BbMarks: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BbMarks() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){

				string namebb = bb->getName();
				GlobalVariable* c1 = make_global_str(M,namebb);

				Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_bb" ,
							Type::getVoidTy( M.getContext() ),
							Type::getInt8PtrTy( M.getContext() ),
							(Type *)0
							));

				Value* EndFn = cast<Value> ( M.getOrInsertFunction( "end_bb" ,
							Type::getVoidTy( M.getContext() ),
							Type::getInt8PtrTy( M.getContext() ),
							(Type *)0
							));

				{
					BasicBlock::iterator insertpos = bb->begin();
					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
#ifdef LLVM29
					CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
					CallInst::Create(InitFn, params, "", insertpos);
#endif
				}

				{
					BasicBlock::iterator insertpos = bb->end(); insertpos--;
					std::vector<Value*> params;
					params.push_back(pointerToArray(M,c1));
#ifdef LLVM29
					CallInst::Create(EndFn, params.begin(), params.end(), "", insertpos);
#else
					CallInst::Create(EndFn, params, "", insertpos);
#endif
				}
			}
		}

		mod_iterator(M, fn){

			string fn_name = fn->getName().str();


			Function::arg_iterator arg_begin = fn->arg_begin();
			Function::arg_iterator arg_end   = fn->arg_end();

			stringstream function_operand_list;
			for( Function::arg_iterator it = arg_begin; it != arg_end; it++ ){
				function_operand_list << operandname(it) << ",";
			}
			string fn_oplist = function_operand_list.str();

			GlobalVariable* c1 = make_global_str(M, fn_name );
			GlobalVariable* c2 = make_global_str(M, fn_oplist);

			//void BeginFn(char* _fn_name, char* fn_oplist);
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "BeginFn" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));

			Function::iterator begin = fn->begin();
			Function::iterator end   = fn->end();

			//cerr << "\e[31m" << fn_name << "\e[0m" << endl;
			if( begin != end ){
				//begin->dump();

				BasicBlock::iterator insertpos = fn->begin()->begin();
				//insertpos++;

				std::vector<Value*> params;
				params.push_back(pointerToArray(M,c1));
				params.push_back(pointerToArray(M,c2));
#ifdef LLVM29
				CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
				CallInst::Create(InitFn, params, "", insertpos);
#endif
				
			}



		}

		return false;

	}
};

struct AllocaInstr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	AllocaInstr() : ModulePass(ID) {}



	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( AllocaInst::classof(in) ){

						AllocaInst* in_a = cast<AllocaInst>(in);

						string nameres = "register" UNDERSCORE + in->getName().str();

						string type = get_type_str(in_a->getAllocatedType());
						string subtype = get_flattened_types( in_a->getAllocatedType() );

						//cerr << "subtype " << subtype << endl;

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, subtype);

						Value* InitFn = cast<Value> ( M.getOrInsertFunction( "alloca_instr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));

						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

					}
				}
			}
		}

		return false;
	}
};

struct GetelementPtr: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	GetelementPtr() : ModulePass(ID) {}



	virtual bool runOnModule(Module &M) {

		mod_iterator(M, fn){
			fun_iterator(fn, bb){
				blk_iterator(bb, in){
					if( GetElementPtrInst::classof(in) ){

						GetElementPtrInst* in_g = cast<GetElementPtrInst>(in);
						Value* pointer = in_g->getPointerOperand();


						GlobalVariable* pointer_global = dyn_cast<GlobalVariable>(pointer);

						string nameres = "register" UNDERSCORE + in->getName().str();

						string nameop1;
						if( pointer_global )
							nameop1 = "global" UNDERSCORE + pointer->getName().str();
						else
							nameop1 = "register" UNDERSCORE + pointer->getName().str();

						
						vector<string> indexes = get_indexes(in_g);
						string indexes_str;
						for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
							indexes_str += *it + ",";
						}

						string offset_tree = get_offset_tree(in_g->getPointerOperand()->getType());

						const PointerType* pointertype = cast<PointerType>(in_g->getPointerOperand()->getType());
						const Type*        pointedtype = pointertype->getElementType();
						int   elementsize = get_size(pointedtype);
						string elementsize_s = itos(elementsize);

						GlobalVariable* c1 = make_global_str(M, nameres);
						GlobalVariable* c2 = make_global_str(M, nameop1);
						GlobalVariable* c3 = make_global_str(M, indexes_str);
						GlobalVariable* c4 = make_global_str(M, offset_tree);
						//GlobalVariable* c5 = make_global_str(M, elementsize_s);

						Value* InitFn;

						InitFn = cast<Value> ( M.getOrInsertFunction( "getelementptr" ,
									Type::getVoidTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									Type::getInt8PtrTy( M.getContext() ),
									//Type::getInt8PtrTy( M.getContext() ),
									(Type *)0
									));


						BasicBlock::iterator insertpos = in; insertpos++;

						std::vector<Value*> params;
						params.push_back(pointerToArray(M,c1));
						params.push_back(pointerToArray(M,c2));
						params.push_back(pointerToArray(M,c3));
						params.push_back(pointerToArray(M,c4));
						//params.push_back(pointerToArray(M,c5));
#ifdef LLVM29
						CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
						CallInst::Create(InitFn, params, "", insertpos);
#endif

					}
				}
			}
		}

		return false;
	}
};

struct BeginEnd: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	BeginEnd() : ModulePass(ID) {}


	virtual bool runOnModule(Module &M) {

		{
			BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "begin_sim" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
#ifdef LLVM29
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
			CallInst::Create(InitFn, params, "", insertpos);
#endif
		}

		{
			//Function::iterator insertpos_f = M.getFunction("main")->end();
			//insertpos_f--;
			Function::iterator insertpos_f = return_bb(M.getFunction("main"));

			BasicBlock::iterator insertpos_b = insertpos_f->end();
			insertpos_b--;

	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "end_sim" ,
						Type::getVoidTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
#ifdef LLVM29
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos_b);
#else
			CallInst::Create(InitFn, params, "", insertpos_b);
#endif
		}

		return false;
	}
};


struct MainArgs: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	MainArgs() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

//#define argv_size 5
//#define argvs_size 10
//#define each_argv_size 3
#define argv_size cmd_option_int("argv_size")
#define argvs_size cmd_option_int("argvs_size")
#define each_argv_size cmd_option_int("each_argv_size")

		// Read number of arguments
		read_options();
		string number_of_args = cmd_option_str("argc");
		number_of_args = (number_of_args=="")?"0":number_of_args;
		int number_of_args_i = stoi(number_of_args);

		// Finds main Function
		Function* fn = M.getFunction("main");
		Function::arg_iterator arg_begin = fn->arg_begin();
		Function::arg_iterator arg_end   = fn->arg_end();
		if(arg_begin == arg_end) return false;

		BasicBlock* fnbegin = fn->begin();
		Instruction* inbegin = fnbegin->begin();

		// Allocate space for argc
		AllocaInst* argc_addr = new AllocaInst(IntegerType::get(M.getContext(), 32), "argc_addr", inbegin );
		
		// Allocate space for argv
		PointerType* PointerTy_4 = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
		ArrayType* ArrayTy_3 = ArrayType::get(PointerTy_4, argv_size);
		AllocaInst*  argv_addr   = new AllocaInst(ArrayTy_3, "argv_addr", inbegin);

		// Allocate space for argvs
		ArrayType* ArrayTy     = ArrayType::get(IntegerType::get(M.getContext(), 8), argvs_size);
		AllocaInst*  argvs      = new AllocaInst(ArrayTy, "argvs", inbegin);


		// Set each argv
		for ( int i = 0; i < number_of_args_i; i++) {

			Instruction* ptr_13;
			Instruction* ptr_14;


			{
				string elem = itos(i);
				ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
				ConstantInt* const_int64_11 = ConstantInt::get(M.getContext(), APInt(64, StringRef(elem), 10));
				std::vector<Value*> ptr_13_indices;
				ptr_13_indices.push_back(const_int64_10);
				ptr_13_indices.push_back(const_int64_11);
				ptr_13 = GetElementPtrInst::Create(argv_addr, ptr_13_indices.begin(), ptr_13_indices.end(), "", inbegin);
			}



			{
				string elem = itos(each_argv_size*i);
				ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
				ConstantInt* const_int64_11 = ConstantInt::get(M.getContext(), APInt(64, StringRef(elem), 10));
				std::vector<Value*> ptr_14_indices;
				ptr_14_indices.push_back(const_int64_10);
				ptr_14_indices.push_back(const_int64_11);
				ptr_14 = GetElementPtrInst::Create(argvs, ptr_14_indices.begin(), ptr_14_indices.end(), "", inbegin);
			}

			new StoreInst(ptr_14, ptr_13, false, inbegin);
		}


		// Set number of argc
		new StoreInst(ConstantInt::get(M.getContext(), APInt(32, StringRef(number_of_args), 10)), argc_addr, false, inbegin);

		// Load argc and argv
		LoadInst* argc = new LoadInst(argc_addr, "argc", false, inbegin);
		//LoadInst* argv = new LoadInst(argv_addr, "argv", false, inbegin);

		// Cast argv instruction
		
		 PointerType* PointerTy_2 = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
		 PointerType* PointerTy_1 = PointerType::get(PointerTy_2, 0);
		CastInst* argv_cast = new BitCastInst(argv_addr, PointerTy_1, "argv_cast", inbegin);

		// Substitute in subsequent instructions
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( StoreInst::classof(in) ){
				string name = in->getOperand(0)->getName().str();
				if(name == "argc"){
					in->setOperand(0, argc);
				}
				if(name == "argv"){
					in->setOperand(0, argv_cast);
				}
			}
		}}

#undef argv_size
#undef argvs_size
#undef each_argv_size

		return false;
	}

};


struct CheckParseable: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	CheckParseable() : ModulePass(ID) {}

	bool get_is_parseable(Module &M){
		if(M.getFunction("llvm.stacksave")) return false;
		if(M.getFunction("malloc")) return false;
		if(M.getFunction("alloca")) return false;
		if(M.getFunction("memmove")) return false;
		if(M.getFunction("llvm.memmove.p0i8.p0i8.i64_entry")) return false;
		if(M.getFunction("r_strncpy")) return false;


		//mod_iterator(M, fn){
		//fun_iterator(fn, bb){
		//blk_iterator(bb, in){
			//if( BinaryOperator::classof(in) && in->getOpcode() == 17) return false;
		//}}}

		return true;
	}

	void output_parseable(bool parseable){
		FILE* file = fopen(tmp_file("parseable").c_str(), "w");
		fprintf(file, "%s\n", parseable?"true":"false" );
		fclose(file);
	}

	virtual bool runOnModule(Module &M) {

		read_options();

		output_parseable(get_is_parseable(M));



		return false;

	}

};



struct MainArgs_2: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	MainArgs_2() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {


		// Read number of arguments
		read_options();
		string args_str = cmd_option_str("sym_argvs");

		if(args_str == "") return false;
		vector<string> tokens = tokenize(args_str, " ");
		int min_argvs = stoi(tokens[0]);
		int max_argvs = stoi(tokens[1]);
		int max_len   = stoi(tokens[2]); max_len++;

		// Finds main Function
		Function* fn = M.getFunction("main");
		Function::arg_iterator arg_begin = fn->arg_begin();
		Function::arg_iterator arg_end   = fn->arg_end();
		if(arg_begin == arg_end) return false;

		BasicBlock* fnbegin = fn->begin();
		Instruction* inbegin = fnbegin->begin();

		// Allocate space for argc
		AllocaInst* argc_addr = new AllocaInst(IntegerType::get(M.getContext(), 32), "argc_addr", inbegin );
		
		// Allocate space for argv
		PointerType* PointerTy_4 = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
		ArrayType* ArrayTy_3 = ArrayType::get(PointerTy_4, max_argvs);
		AllocaInst*  argv_addr   = new AllocaInst(ArrayTy_3, "argv_addr", inbegin);

		// Allocate space for argvs
		ArrayType* ArrayTy     = ArrayType::get(IntegerType::get(M.getContext(), 8), max_len*max_argvs);
		AllocaInst*  argvs      = new AllocaInst(ArrayTy, "argvs", inbegin);


		// Set each argv
		for ( int i = 0; i < max_argvs; i++) {

			Instruction* ptr_13;
			Instruction* ptr_14;
			Instruction* ptr_15;


			{
				string elem = itos(i);
				ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
				ConstantInt* const_int64_11 = ConstantInt::get(M.getContext(), APInt(64, StringRef(elem), 10));
				std::vector<Value*> ptr_13_indices;
				ptr_13_indices.push_back(const_int64_10);
				ptr_13_indices.push_back(const_int64_11);
#ifdef LLVM29
				ptr_13 = GetElementPtrInst::Create(argv_addr, ptr_13_indices.begin(), ptr_13_indices.end(), "", inbegin);
#else
				ptr_13 = GetElementPtrInst::Create(argv_addr, ptr_13_indices, "", inbegin);
#endif
			}



			{
				string elem = itos(max_len*i);
				ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
				ConstantInt* const_int64_11 = ConstantInt::get(M.getContext(), APInt(64, StringRef(elem), 10));
				std::vector<Value*> ptr_14_indices;
				ptr_14_indices.push_back(const_int64_10);
				ptr_14_indices.push_back(const_int64_11);
#ifdef LLVM29
				ptr_14 = GetElementPtrInst::Create(argvs, ptr_14_indices.begin(), ptr_14_indices.end(), "", inbegin);
#else
				ptr_14 = GetElementPtrInst::Create(argvs, ptr_14_indices, "", inbegin);
#endif
			}

			{
				string elem = itos(max_len*i + max_len - 1);
				ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(64, StringRef("0"), 10));
				ConstantInt* const_int64_11 = ConstantInt::get(M.getContext(), APInt(64, StringRef(elem), 10));
				std::vector<Value*> ptr_15_indices;
				ptr_15_indices.push_back(const_int64_10);
				ptr_15_indices.push_back(const_int64_11);
#ifdef LLVM29
				ptr_15 = GetElementPtrInst::Create(argvs, ptr_15_indices.begin(), ptr_15_indices.end(), "", inbegin);
#else
				ptr_15 = GetElementPtrInst::Create(argvs, ptr_15_indices, "", inbegin);
#endif
			}

			ConstantInt* const_int64_10 = ConstantInt::get(M.getContext(), APInt(8, StringRef("0"), 10));
			new StoreInst(ptr_14, ptr_13, false, inbegin);
			new StoreInst(const_int64_10, ptr_15, false, inbegin);
		}



		// Load argc and argv
		LoadInst* argc = new LoadInst(argc_addr, "argc", false, inbegin);
		//LoadInst* argv = new LoadInst(argv_addr, "argv", false, inbegin);

		// Cast argv instruction
		PointerType* PointerTy_2 = PointerType::get(IntegerType::get(M.getContext(), 8), 0);
		PointerType* PointerTy_1 = PointerType::get(PointerTy_2, 0);
		CastInst* argv_cast = new BitCastInst(argv_addr, PointerTy_1, "argv_cast", inbegin);

		// Substitute in subsequent instructions
		fun_iterator(fn, bb){
		blk_iterator(bb, in){
			if( StoreInst::classof(in) ){
				string name = in->getOperand(0)->getName().str();
				if(name == "argc"){
					in->setOperand(0, argc);
				}
				if(name == "argv"){
					in->setOperand(0, argv_cast);
				}
			}
		}}

		// Icmp for minimum argc
		BasicBlock::iterator insertpos = argv_cast; while( insertpos->getName() != "retval" ) insertpos++; insertpos++;
		ConstantInt* const_int32_4 = ConstantInt::get(M.getContext(), APInt(32, StringRef(itos(min_argvs)), 10));
		ICmpInst* int1_8 = new ICmpInst(insertpos, ICmpInst::ICMP_SLT,argc, const_int32_4, "min");

		// Icmp for maximum argc
		Instruction* insertpos_2 = int1_8;
		ConstantInt* const_int32_4_2 = ConstantInt::get(M.getContext(), APInt(32, StringRef(itos(max_argvs)), 10));
		ICmpInst* int1_8_2 = new ICmpInst(insertpos_2, ICmpInst::ICMP_SGT,argc, const_int32_4_2, "max");


		// First slice
		BasicBlock::iterator splitpos = int1_8_2; splitpos++; splitpos++;
		fnbegin->splitBasicBlock(splitpos);

		// Second slice
		BasicBlock::iterator splitpos_2 = int1_8_2; splitpos_2++;
		fnbegin->splitBasicBlock(splitpos_2);

		// Basic Blocks
		Function::iterator bb1 = fn->begin();
		Function::iterator bb2 = bb1; bb2++;
		Function::iterator bb3 = bb2; bb3++;
		Function::iterator bbl = fn->end(); bbl--;

		// Change terminator
		bb1->getTerminator()->eraseFromParent();
		BranchInst::Create(bbl,bb2, int1_8_2, bb1);

		// Change terminator
		bb2->getTerminator()->eraseFromParent();
		BranchInst::Create(bbl,bb3, int1_8, bb2);

		return false;

	}

};

struct GlobalInit: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	GlobalInit() : ModulePass(ID) {}

	map<string, int> given_addr;
	int current_addr = 0;


	bool is_number(const std::string& s) {
	
		//printf("\e[33m is_number \e[0m %s\n", s.c_str() );
	
		if( s== "true" || s== "false") return true;
	
		if(s.substr(0,1) == "-") return is_number(s.substr(1));
	
		//printf("%s\n", s.substr(0,s.find(".")).c_str() );
		//printf("%s\n", s.substr(s.find(".")+1).c_str() );
		if( s.find(".") != string::npos ) return 
			is_number(s.substr(0,s.find("."))) &&
			is_number(s.substr(s.find(".")+1));
	
	
		if( s.find("e") != string::npos ) return 
			is_number(s.substr(0,s.find("e"))) &&
			is_number(s.substr(s.find("e")+1));
	
		std::string::const_iterator it = s.begin();
		while (it != s.end() && std::isdigit(*it)) ++it;
		return !s.empty() && it == s.end();
	}


	string close_str(string offset_tree){
	
		int depth = 0;
		for ( unsigned int i = 0; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0) return offset_tree.substr(0,i+1);
		}
	
		assert(0 && "Unbalanced tree");
	
	}
	
	string trimpar(string str){
	
		int n1 = str.find_first_not_of("()");
		int n2 = str.substr(n1).find_first_not_of("0123456789-");
		string firstnum = str.substr(n1).substr(0,n2);
		//printf("trimpar %s %s %d %d %s\n", str.c_str(), str.substr(n1).c_str(),  n1, n2, str.substr(n1).substr(0,n2).c_str() );
		assert( is_number(firstnum) && "ret is not a number");
		return firstnum;
	}

	bool has_index(string offset_tree, int index){
	
		int depth = -1;
		int nelem = -1;
		for ( unsigned int i = 1; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0 && offset_tree[i] == '(' ){
				nelem++;
			}
			if(nelem == index){
				return true;
	
			}
		}
	
		return false;
	}

	int get_ini_elem(int nelem_target, string offset_tree){
	
		int depth = -1;
		int nelem = -1;
		for ( unsigned int i = 1; i < offset_tree.size(); i++) {
			if(offset_tree[i] == '(') depth++;
			if(offset_tree[i] == ')') depth--;
			if(depth == 0 && offset_tree[i] == '(' ){
				nelem++;
				//printf("elem %d at %d\n", nelem, i);
			}
			if(nelem == nelem_target){
				//printf("get_ini_elem %d %s : %d\n", nelem_target, offset_tree.c_str(), i);
				return i;
	
			}
		}
	
		assert(0 && "Unbalanced tree");
	
	}


	int get_offset(vector<int> indexes, string offset_tree){
	
	
		//for( vector<string>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
			//debug && printf("\e[33m %s ", it->c_str() );
		//} debug && printf(" --- ");
		//debug && printf(" offset %s\e[0m\n", offset_tree.c_str() );
		
		int index_0 = indexes[0];
	
		//debug && printf("\e[33m %s %s \e[0m\n", indexes[0].c_str(), realvalue(indexes[0]).c_str() );
	
		//int realvalue_index_0 = stoi(realvalue_index_0_s);
	
		if( has_index(offset_tree, index_0) ){
	
			int ini_elem = get_ini_elem(index_0, offset_tree);
			string right_str = offset_tree.substr(ini_elem);
			string elem_str = close_str(right_str);
			//printf("elem_str %s\n", elem_str.c_str());
	
			vector<int>::iterator first_it = indexes.begin(); first_it++;
			vector<int> rem_indexes = vector<int>(first_it, indexes.end());
	
			if( rem_indexes.size() ){
				return get_offset(rem_indexes, elem_str);
			} else {
				return stoi(trimpar(elem_str));
			}
	
		} else {
			vector<string> tokens = tokenize(offset_tree, "(),");
			string size_s = tokens[tokens.size()-1];
			int size = stoi(size_s);
			//printf("offset_tree %s realvalue_index_0 %d size_s %s\n", offset_tree.c_str(), realvalue_index_0, size_s.c_str());
			return size*index_0;
		}
	
	}




	string get_flattened_vals( Constant* constant ){

		//cerr << "get_flattened_vals ";
		//constant->dump();

		//cerr << "type" << endl;
		//cerr << ConstantUndefValue::classof(constant) << endl;

		ConstantInt*         constant_int          = dyn_cast<ConstantInt>(constant);
		ConstantArray*       constant_array        = dyn_cast<ConstantArray>(constant);
		ConstantFP*          constant_float        = dyn_cast<ConstantFP>(constant);
		ConstantStruct*      constant_struct       = dyn_cast<ConstantStruct>(constant);
		ConstantPointerNull* constant_pointer_null = dyn_cast<ConstantPointerNull>(constant);
		GlobalValue*         constant_global       = dyn_cast<GlobalValue>(constant);
		GEPOperator*         gepop                 = dyn_cast<GEPOperator>(constant);
		ConstantExpr*        castop                = dyn_cast<ConstantExpr>(constant);

		//cerr << "constant_global: ";
		//constant_global->dump();


		string type = get_type_str(constant->getType());

		//cerr << "type " << type << endl;
		//if(constant_global)
		//cerr << "name " << constant_global->getName().str() << endl;

		if( type == "IntegerTyID"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID32"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID16"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID64"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "IntegerTyID8"){
			int64_t val = constant_int->getSExtValue();
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "FloatTyID"){
			float val = floatvalue_fl(constant_float);
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "DoubleTyID"){
			float val = floatvalue_fl(constant_float);
			stringstream nameop1_ss; nameop1_ss << "constant" UNDERSCORE << type << UNDERSCORE << val;
			return nameop1_ss.str();
		} else if( type == "StructTyID"){

			//cerr << "----- struct ------" << endl;

			const StructType* struct_type = cast<StructType>(constant->getType());

			//struct_type->dump();
			//constant->dump();

			string aux;

			if(constant->isNullValue()){

				string flattenedtypes = get_flattened_types(struct_type);
				vector<string> tokens = tokenize(flattenedtypes, ",");

				for ( unsigned int i = 0; i < tokens.size(); i++) {
					aux += "X,";
				}


			} else {

				for ( unsigned int i = 0; i < struct_type->getNumElements(); i++) {

					Value*         operand_i    = constant_struct->getOperand(i);

					//cerr << "operand_i" << endl;
					//operand_i->dump();

					Constant*      operand_i_const = dyn_cast<Constant>(operand_i);

					assert(operand_i_const && "Operand i must be constant");

					aux += get_flattened_vals(operand_i_const) + ",";
				}
			}

			return aux;

		} else if( type == "ArrayTyID" ){

			//cerr << "----- array ------" << endl;

			const ArrayType* array_type = cast<ArrayType>(constant->getType());

			string aux;

			if(constant->isNullValue()){

				string flattenedtypes = get_flattened_types(array_type);
				vector<string> tokens = tokenize(flattenedtypes, ",");

				for ( unsigned int i = 0; i < tokens.size(); i++) {
					aux += "X,";
				}


			} else {




				for ( unsigned int i = 0; i < array_type->getNumElements(); i++) {

					Value*         operand_i    = constant_array->getOperand(i);

					//cerr << "operand_i" << endl;
					//operand_i->dump();

					Constant*      operand_i_const = dyn_cast<Constant>(operand_i);

					assert(operand_i_const && "Operand i must be constant");

					aux += get_flattened_vals(operand_i_const) + ",";
				}
			}

			return aux;
			
		} else if( type == "PointerTyID" ){

			if(constant_pointer_null){
				return "constant_" + type + "_0";
			} else if (constant_global) {
				//constant_global->dump();
				//cerr << "address of : " << "global_" + constant_global->getName().str() << endl;
				//cerr << "is: " << given_addr["global_" + constant_global->getName().str()];
				return "constant_" + type + "_" + itos(given_addr["global_" + constant_global->getName().str()]);
			} else if(gepop){
				//cerr << "gepop " << endl;
				//gepop->dump();
				//gepop->getOperand(0)->getType()->dump();
				
				string name_base = "global_" + gepop->getOperand(0)->getName().str();

				
				string offset_tree = get_offset_tree(gepop->getType());

				int base = given_addr[name_base];
				//cerr << "name_base " << name_base << " base " << base << endl;

				vector<int> indexes = get_indexes_gepop(gepop);

				string indexes_str;
				for( vector<int>::iterator it = indexes.begin(); it != indexes.end(); it++ ){
					indexes_str += itos(*it) + ",";
				}
				


				int offset = get_offset(indexes, offset_tree);

				int addr = base + offset;

				//cerr << "tree " << offset_tree << " indexes " << indexes_str << " offset " << offset << " addr " << addr << endl;

				return "constant_" + type + "_" + itos(addr);
			} else if(castop){
				string name_base = "global_" + castop->getOperand(0)->getName().str();

				int base = given_addr[name_base];

				return "constant_" + type + "_" + itos(base);



			} else {
				constant->dump();
				assert(0 && "Error in global pointer initialization");
			}



		} else {
			cerr << type << endl;
			assert( 0 && "Unknown initializer type");
		}

	}

	void get_given_addr(Module& M){

		glo_iterator(M,gl){
			string             name         = string("global" UNDERSCORE) + gl->getName().str();
			const PointerType* pointertype  = cast<PointerType>(gl->getType());
			const Type*        type_t       = pointertype->getElementType();
			given_addr[name] = current_addr;
			current_addr += get_size(type_t);
		}
	}

	virtual bool runOnModule(Module &M) {

		vector<VarInit> global_var_inits;

		get_given_addr(M);

		glo_iterator(M,gl){

			//cerr << "--- global ";
			//gl->dump();
			//cerr << "hasInitializer " << gl->hasInitializer() << endl;

			string             name         = string("global" UNDERSCORE) + gl->getName().str();
			const PointerType* pointertype  = cast<PointerType>(gl->getType());
			const Type*        type_t       = pointertype->getElementType();

			GlobalVariable*    global_var   = cast<GlobalVariable>(gl);

			string types = get_flattened_types(type_t);
			string vals;

			if(gl->hasInitializer()){
				Constant* constant     = global_var->getInitializer();
				vals  = get_flattened_vals(constant);
			} else {
				vector<string> tokens = tokenize(types,",");
				for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
					vals += "X,";
				}
			}

			//cerr << "types " << types << endl;
			//cerr << "vals  " << vals  << endl;

			VarInit varinit = {name, types, vals };

			global_var_inits.push_back(varinit);


			//cerr << "name " << name << " addr " << current_addr << endl;

		}

		BasicBlock::iterator insertpos = M.getFunction("main")->begin()->begin();
		for( vector<VarInit>::iterator it = global_var_inits.begin(); it != global_var_inits.end(); it++ ){


			string name           = it->name;
			string type           = it->type;
			string initialization = it->initialization;

			GlobalVariable* c1 = make_global_str(M, name);
			GlobalVariable* c2 = make_global_str(M, type);
			GlobalVariable* c3 = make_global_str(M, initialization);
	
			Value* InitFn = cast<Value> ( M.getOrInsertFunction( "global_var_init" ,
						Type::getVoidTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						Type::getInt8PtrTy( M.getContext() ),
						(Type *)0
						));
	
			std::vector<Value*> params;
			params.push_back(pointerToArray(M,c1));
			params.push_back(pointerToArray(M,c2));
			params.push_back(pointerToArray(M,c3));
#ifdef LLVM29
			CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
			CallInst::Create(InitFn, params, "", insertpos);
#endif

		}

		Value* InitFn = cast<Value> ( M.getOrInsertFunction( "pointer_ranges" , Type::getVoidTy( M.getContext() ), (Type *)0));
		std::vector<Value*> params;
#ifdef LLVM29
		CallInst::Create(InitFn, params.begin(), params.end(), "", insertpos);
#else
		CallInst::Create(InitFn, params, "", insertpos);
#endif


		return false;
	}
};

struct All: public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	All() : ModulePass(ID) {}

	virtual bool runOnModule(Module &M) {

		read_options();

		cerr << "AddAssertFn    " << endl; fflush(stderr); {AddAssertFn      pass;   pass.runOnModule(M);}
		cerr << "RmErrorFn      " << endl; fflush(stderr); {RmErrorFn        pass;   pass.runOnModule(M);}
		cerr << "RmPutsFn       " << endl; fflush(stderr); {RmPutsFn         pass;   pass.runOnModule(M);}
		cerr << "RmXBool        " << endl; fflush(stderr); {RmXBool          pass;   pass.runOnModule(M);}
		cerr << "MainArgs_2     " << endl; fflush(stderr); {MainArgs_2       pass;   pass.runOnModule(M);}
		//cerr << "Demangle       " << endl; fflush(stderr); {Demangle         pass;   pass.runOnModule(M);}
		cerr << "SwitchInstr    " << endl; fflush(stderr); {SwitchInstr      pass;   pass.runOnModule(M);}
		cerr << "FillNames      " << endl; fflush(stderr); {FillNames        pass;   pass.runOnModule(M);}
		cerr << "SeparateGetElm " << endl; fflush(stderr); {SeparateGetElm   pass;   pass.runOnModule(M);}
		cerr << "GlobalInit     " << endl; fflush(stderr); {GlobalInit       pass;   pass.runOnModule(M);}
		cerr << "CallInstr      " << endl; fflush(stderr); {CallInstr        pass;   pass.runOnModule(M);}
		cerr << "SpecialCall    " << endl; fflush(stderr); {SpecialCall      pass;   pass.runOnModule(M);}
		cerr << "SelectInstr    " << endl; fflush(stderr); {SelectInstr      pass;   pass.runOnModule(M);}
		cerr << "BinaryOp       " << endl; fflush(stderr); {BinaryOp         pass;   pass.runOnModule(M);}
		cerr << "CastInstr      " << endl; fflush(stderr); {CastInstr        pass;   pass.runOnModule(M);}
		cerr << "LoadStore      " << endl; fflush(stderr); {LoadStore        pass;   pass.runOnModule(M);}
		cerr << "IcmpInstr      " << endl; fflush(stderr); {IcmpInstr        pass;   pass.runOnModule(M);}
		cerr << "BrInstr        " << endl; fflush(stderr); {BrInstr          pass;   pass.runOnModule(M);}
		cerr << "BbMarks        " << endl; fflush(stderr); {BbMarks          pass;   pass.runOnModule(M);}
		cerr << "AllocaInstr    " << endl; fflush(stderr); {AllocaInstr      pass;   pass.runOnModule(M);}
		cerr << "BeginEnd       " << endl; fflush(stderr); {BeginEnd         pass;   pass.runOnModule(M);}
		cerr << "GetelementPtr  " << endl; fflush(stderr); {GetelementPtr    pass;   pass.runOnModule(M);}
		cerr << "Memcpy         " << endl; fflush(stderr); {Memcpy           pass;   pass.runOnModule(M);}
		cerr << "ChAssumeFn     " << endl; fflush(stderr); {ChAssumeFn       pass;   pass.runOnModule(M);}
		//cerr << "ChAssertFn     " << endl; fflush(stderr); {ChAssertFn       pass;   pass.runOnModule(M);}
		//cerr << "RmInstr        " << endl; fflush(stderr); {RmInstr          pass;   pass.runOnModule(M);}
		//cerr << "RmIndetFn      " << endl; fflush(stderr); {RmIndetFn        pass;   pass.runOnModule(M);}
		cerr << "ChAlloc        " << endl; fflush(stderr); {ChAlloc          pass;   pass.runOnModule(M);}
		cerr << "FPointerhook   " << endl; fflush(stderr); {FPointerhook     pass;   pass.runOnModule(M);}

		return false;
	}
};





// Identifiers

char FillNames::ID = 0;
static RegisterPass<FillNames> FillNames(             "instr_fill_names"         , "Fills operands and Block Names                      " );

char FPointerhook::ID = 0;
static RegisterPass<FPointerhook> FPointerhook(       "instr_fpointerhook"       , "Function Pointer Hook                               " );

char FunctionNames::ID = 0;
static RegisterPass<FunctionNames> FunctionNames(     "instr_function_names"     , "Change names of standard functions                  " );

char Demangle::ID = 0;
static RegisterPass<Demangle> Demangle(               "instr_demangle"           , "Demangle names                                      " );

char BinaryOp::ID = 0;
static RegisterPass<BinaryOp> BinaryOp(               "instr_binaryop"           , "Instrument binary operations                        " );

char RmXBool::ID = 0;
static RegisterPass<RmXBool> RmXBool(                 "instr_rmxbool"            , "Remove xor boolean                                  " );

char RmIndetFn::ID = 0;
static RegisterPass<RmIndetFn> RmIndetFn(             "instr_rmindet"            , "Remove indetermination functions                    " );

char RmAssumeFn::ID = 0;
static RegisterPass<RmAssumeFn> RmAssumeFn(           "instr_rmassume"           , "Remove assume functions                             " );

char RmErrorFn::ID = 0;
static RegisterPass<RmErrorFn> RmErrorFn(             "instr_rmerror"            , "Remove error functions                              " );

char RmPutsFn::ID = 0;
static RegisterPass<RmPutsFn> RmPutsFn(               "instr_rmputs"             , "Remove puts/printf functions                        " );

char RmPthread::ID = 0;
static RegisterPass<RmPthread> RmPthread(             "instr_rmpthread"          , "Remove pthread functions                            " );

char RmMemcpyFn::ID = 0;
static RegisterPass<RmMemcpyFn> RmMemcpyFn(           "instr_rmmemcpy"           , "Remove llvm.memcpy functions                        " );

char RmMalloc::ID = 0;
static RegisterPass<RmMalloc> RmMalloc(               "instr_rmmalloc"           , "Remove memory allocation functions                  " );

char ChAssumeFn::ID = 0;
static RegisterPass<ChAssumeFn> ChAssumeFn(           "instr_chassume"           , "Change assume functions                             " );

char ChAlloc::ID = 0;
static RegisterPass<ChAlloc> ChAlloc(                 "instr_challoc"            , "Change alloca functions                             " );

char ChAssertFn::ID = 0;
static RegisterPass<ChAssertFn> ChAssertFn(           "instr_chassert"           , "Change assert functions                             " );

char AddAssertFn::ID = 0;
static RegisterPass<AddAssertFn> AddAssertFn(         "instr_addassert"           , "Add assert functions                               " );

char RmInstr::ID = 0;
static RegisterPass<RmInstr> RmInstr(                 "remove_instr"             , "Remove instructions                                 " );

char SelectInstr::ID = 0;
static RegisterPass<SelectInstr> SelectInstr(         "instr_select"             , "Instrument select operations                        " );

char IsolateFunction::ID = 0;
static RegisterPass<IsolateFunction> IsolateFunction( "isolate_function"         , "Isolate a single function for model creation        " );

char CastInstr::ID = 0;
static RegisterPass<CastInstr> CastInstr(             "instr_castinstr"          , "Instrument cast operations                          " );

char LoadStore::ID = 0;
static RegisterPass<LoadStore> LoadStore(             "instr_loadstore"          , "Instrument load/store operations                    " );

char SeparateGetElm::ID = 0;
static RegisterPass<SeparateGetElm> SeparateGetElm  ( "separate_getelem"         , "Separate GetElementPtr from load/store instructions " );

char IcmpInstr::ID = 0;
static RegisterPass<IcmpInstr> IcmpInstr(             "instr_icmpinstr"          , "Instrument comparison operations                    " );

char BrInstr::ID = 0;
static RegisterPass<BrInstr> BrInstr(                 "instr_brinstr"            , "Instrument branch operations                        " );

char SwitchInstr::ID = 0;
static RegisterPass<SwitchInstr> SwitchInstr(         "instr_switch"             , "Instrument switch operations                        " );

char CallInstr::ID = 0;
static RegisterPass<CallInstr> CallInstr(             "instr_callinstr"          , "Instrument call operations                          " );

char Memcpy::ID = 0;
static RegisterPass<Memcpy> Memcpy(                   "instr_memcpy"             , "Instrument memcpy operations                        " );

char ExternalFn::ID = 0;
static RegisterPass<ExternalFn> ExternalFn(           "list_external_functions"  , "Instrument call operations                          " );

char SpecialCall::ID = 0;
static RegisterPass<SpecialCall> SpecialCall(         "instr_specialcall"        , "Instrument call operations                          " );

char BbMarks::ID = 0;
static RegisterPass<BbMarks> BbMarks(                 "instr_bbmarks"            , "Instrument Basic-Blocks                             " );

char AllocaInstr::ID = 0;
static RegisterPass<AllocaInstr> AllocaInstr(         "instr_alloca"             , "Instrument alloca operations                        " );

char GetelementPtr::ID = 0;
static RegisterPass<GetelementPtr> GetelementPtr(     "instr_getelementptr"      , "Instrument getelementptr operations                 " );

char BeginEnd::ID = 0;
static RegisterPass<BeginEnd> BeginEnd(               "instr_beginend"           , "Instrument begin and end of program                 " );

char GlobalInit::ID = 0;
static RegisterPass<GlobalInit> GlobalInit(           "instr_globalinit"         , "Initialize global variables                         " );

char MainArgs::ID = 0;
static RegisterPass<MainArgs> MainArgs(               "main_args"                , "main arguments                                      " );

char MainArgs_2::ID = 0;
static RegisterPass<MainArgs_2> MainArgs_2(           "main_args_2"              , "main arguments                                      " );

char CheckParseable::ID = 0;
static RegisterPass<CheckParseable> CheckParseable(   "check_parseable"          , "checks if the program contains extraneous things    " );

char All::ID = 0;
static RegisterPass<All> All(                         "instr_all"                , "Instrument all operations                           " );


