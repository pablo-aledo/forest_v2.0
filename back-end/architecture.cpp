/*
 * =====================================================================================
 * /
 * |     Filename:  architecture.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/15/2014 05:34:24 PM
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


#include "utils.h"
#include <string.h>

using namespace std;

string hex_representation(int in, string type){
	char b[20];

	if(type == "IntegerTyID32")
		sprintf(b, "%08x", in);
	else if(type == "DoubleTyID")
		sprintf(b, "%16x", in);
	else if(type == "Int")
		sprintf(b, "%08x", in);
	else if(type == "bool")
		sprintf(b, "%08x", in);
	else if(type == "IntegerTyID16")
		sprintf(b, "%04x", in);
	else if(type == "IntegerTyID64")
		sprintf(b, "%016x", in);
	else if(type == "IntegerTyID8")
		sprintf(b, "%02x", in);
	else if(type == "PointerTyID")
		sprintf(b, "%016x", in);
	else if(type == "Pointer")
		sprintf(b, "%016x", in);
	else{
		printf("%s\n", type.c_str());
		assert(0 && "Unknown type");
	}

	//printf("internal representation in %s a %d b %s\n", in.c_str(), a, b);
	return "#x" + string(b);
}


unsigned int bits(string type){
	//printf("bits %s\n", type.c_str());
	if(type == "IntegerTyID32") return 32;
	else if(type == "IntegerTyID16") return 16;
	else if(type == "DoubleTyID") return 64;
	else if(type == "IntegerTyID64") return 64;
	else if(type == "IntegerTyID8" ) return 8;
	else if(type == "Int" ) return 32;
	else if(type == "PointerTyID" ) return 64;
	else if(type == "FloatTyID" ) return 32;
	else if(type == "Pointer" ) return 64;
	else if(type == "bool" ) return 8;
	else{
		printf("unknown_type %s\n", type.c_str());
		assert(0 && "Unknown type");
	}

}

string make_unsigned(string value, string type){

	string ret_s;
	int ret_i;
	int value_i = stoi(value);


	if( value_i < 0){
		ret_i = (1 << bits(type)) - ((~value_i) + 1);
	} else {
		ret_i = value_i;
	}

	return itos(ret_i);
}


string make_signed(string value, string type){

	string ret_s;
	int ret_i;
	int value_i = stoi(value);


	if( value_i > (1 << bits(type)) - 1 ){
		ret_i = -(1 << bits(type)) + (value_i - (1 << bits(type)));
	} else {
		ret_i = value_i;
	}

	return itos(ret_i);
}



string trunc(string src, string dst_type){

	int ret_i;

	     if(dst_type == "IntegerTyID8"   ) ret_i = (char) stoi(src);
	else if(dst_type == "IntegerTyID32"  ) ret_i = (int) stoi(src);
	else if(dst_type == "IntegerTyID16"  ) ret_i = (short) stoi(src);
	else if(dst_type == "DoubleTyID"     ) ret_i = (double) stoi(src);
	else if(dst_type == "IntegerTyID64"  ) ret_i = (long) stoi(src);
	else if(dst_type == "Int"            ) ret_i = (int) stoi(src);
	else if(dst_type == "FloatTyID"      ) ret_i = (float) stoi(src);
	else if(dst_type == "bool"           ) ret_i = (int) stoi(src);
	else assert(0 && "Unknown type");

	if( ret_i < 0 ) ret_i = (1 << bits(dst_type)) + ret_i;

	return itos(ret_i);

}

string hex_representation_2(int in, string type){
	char b[20];

	if(type == "IntegerTyID32")
		sprintf(b, "%08x", in);
	else if(type == "DoubleTyID")
		sprintf(b, "%16x", in);
	else if(type == "Int")
		sprintf(b, "%08x", in);
	else if(type == "bool")
		sprintf(b, "%08x", in);
	else if(type == "IntegerTyID16")
		sprintf(b, "%04x", in);
	else if(type == "IntegerTyID64")
		sprintf(b, "%016x", in);
	else if(type == "IntegerTyID8")
		sprintf(b, "%02x", in);
	else if(type == "PointerTyID")
		sprintf(b, "%016x", in);
	else if(type == "Pointer")
		sprintf(b, "%016x", in);
	else{
		printf("unknown_type %s\n", type.c_str());
		assert(0 && "Unknown type");
	}

	//printf("b: %s type: %s\n", b, type.c_str()); fflush(stdout);

	if(in < 0){
		//printf("in < 0\n");
		if(strlen(b) > bits(type)){
			//printf("a\n");
			string ret = "#x";
			for ( int i = strlen(b); i < bits(type); i++) {
				ret += "f";
			}
			return ret + string(b);
		} else {
			//printf("b\n");
			return "#x" + string(b).substr(strlen(b) - bits(type)/4);
		}
	} else {
		return "#x" + string(b);
	}
}



int get_n_bits(string type){
	return bits(type);
}


string internal_representation_int(int in, string type, string solver){

	char b[20];
	if( solver == "bitvector" || solver == "double" ){
		if(type == "IntegerTyID32"){
			sprintf(b, "#x%08x", (in < 0)?((1 << 32) + in):in);
		} else if (type == "IntegerTyID64"){
			sprintf(b, "#x%016x", (in < 0)?((1 << 64) + in):in);
		} else if (type == "IntegerTyID1"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 8) + in):in);
		} else if (type == "IntegerTyID16"){
			sprintf(b, "#x%04x", (in < 0)?((1 << 16) + in):in);
		} else if (type == "IntegerTyID8"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 8) + in):in);
		} else if (type == "Int"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 32) + in):in);
		} else if(type == "PointerTyID"){
			sprintf(b, "#x%016x", (in < 0)?((1 << 64) + in):in);
		} else {
			//cerr << "type " << type << endl;
			assert(0 && "Unknown type");
		}

	} else if(solver == "real_integer"){
		sprintf(b, "%d", in);
	} else {
		assert(0 && "Unknown solver");
	}

	return string(b);
}

string internal_representation_float(float in, string type, string solver){
	char b[20];

	if( solver == "bitvector")
		sprintf(b, "#x%02x", in);
	else if( solver == "real_integer" )
		sprintf(b, "%d", in);
	else
		assert(0 && "Unknown solver");


	return string(b);
}


int primary_size( string type_str ){

	if( type_str == "IntegerTyID32" ) return 4;
	if( type_str == "IntegerTyID16" ) return 2;
	if( type_str == "IntegerTyID8" ) return 1;
	if( type_str == "IntegerTyID64" ) return 8;
	if( type_str == "PointerTyID" ) return 8; // <
	if( type_str == "FloatTyID" ) return 4;
	if( type_str == "DoubleTyID" ) return 8;

	//cerr << type_str << endl;
	assert(0 && "Unknown type");

}


int get_size(string type){

	if( type == "IntegerTyID32" )
		return 4;

	if( type == "DoubleTyID" )
		return 8;

	if( type == "FloatTyID" )
		return 8;

	if( type == "IntegerTyID8" )
		return 1;

	if( type == "IntegerTyID16" )
		return 2;

	if( type == "IntegerTyID64" )
		return 8;

	if( type == "int" )
		return 4;

	if( type == "PointerTyID")
		return 8; // <

	if( type == "FunctionTyID")
		return 1;


	if( type.find(',') != string::npos ){
		int sum = 0;
		vector<string> tokens = tokenize(type,",");
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			sum += get_size(*it);
		}
		return sum;
	}


	printf("get_size type %s\n", type.c_str());

	assert(0 && "Unknown type");

}


string concat_begin(int size_bits, int num){
	printf("bits %d\n", size_bits);
	char ret[30];
	if(size_bits ==  8) sprintf(ret, "#x%02x", num);
	else if(size_bits == 16) sprintf(ret, "#x%04x", num);
	else if(size_bits == 24) sprintf(ret, "#x%06x", num);
	else if(size_bits == 32) sprintf(ret, "#x%08x", num);
	else assert(0 && "Unknown number of bits");
	return string(ret);
}

string sign_ext(int bits_src, int bits_dst, string content){

	int size_bits = bits_dst - bits_src;


	string zeros = "#x";
	for ( unsigned int i = 0; i < size_bits/4; i++) {
		zeros += "0";
	}

	string ones = "#x";
	for ( unsigned int i = 0; i < size_bits/4; i++) {
		ones += "f";
	}

	stringstream ret;
	int bit = bits_src - 1;
	ret << "(ite (= ((_ extract " << bit << " " << bit << ") " << content << ") #b1) " << ones << " " << zeros << ")";

	return ret.str();

}


string zero_ext(int bits_src, int bits_dst, string content){

	int size_bits = bits_dst - bits_src;


	string zeros = "#x";
	for ( unsigned int i = 0; i < size_bits/4; i++) {
		zeros += "0";
	}

	stringstream ret;
	ret << zeros;

	return ret.str();

}
