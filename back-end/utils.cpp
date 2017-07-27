/*
 * =====================================================================================
 * /
 * |     Filename:  utils.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:55:42 AM
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
#include "options.h"

extern Options* options;

#define debug true

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

string close_str(string offset_tree){

	int depth = 0;
	for ( unsigned int i = 0; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0) return offset_tree.substr(0,i+1);
	}

	assert(0 && "Unbalanced tree");

}


string parameter(string input){

	//printf("parameter %s\n", input.c_str());

	if(input[0] == '(') return close_str(input);
	else return tokenize(input, "() ")[0];

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

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

bool is_hex_digit(char a){
	if(a == '0') return true;
	if(a == '1') return true;
	if(a == '2') return true;
	if(a == '3') return true;
	if(a == '4') return true;
	if(a == '5') return true;
	if(a == '6') return true;
	if(a == '7') return true;
	if(a == '8') return true;
	if(a == '9') return true;
	if(a == 'a') return true;
	if(a == 'b') return true;
	if(a == 'c') return true;
	if(a == 'd') return true;
	if(a == 'e') return true;
	if(a == 'f') return true;
	return false;
}

bool is_function(std::string name){
	return name.substr(0, 8) == "function" || name.substr(0,22) == "constant_FunctionTyID_";
}

bool is_number(const std::string& s) {

	//printf("\e[33m is_number \e[0m %s\n", s.c_str() );

	if( s== "true" || s== "false") return true;

	if(s.substr(0,1) == "-") return is_number(s.substr(1));

	if(s.substr(0,2) == "#x") return is_number(s.substr(2));

	//printf("%s\n", s.substr(0,s.find(".")).c_str() );
	//printf("%s\n", s.substr(s.find(".")+1).c_str() );
	if( s.find(".") != string::npos ) return 
		is_number(s.substr(0,s.find("."))) &&
		is_number(s.substr(s.find(".")+1));


	//if( s.find("e") != string::npos ) return 
		//is_number(s.substr(0,s.find("e"))) &&
		//is_number(s.substr(s.find("e")+1));

	std::string::const_iterator it = s.begin();
	while (it != s.end() && is_hex_digit(*it)) ++it;
	return !s.empty() && it == s.end();
}

int count(string name, string character){

    int n = 0;
    string::size_type sz = 0;

    while ( (sz = name.find (character,sz) ) != string::npos  ){
        sz++; /*otherwise you start searching at your previous match*/
        n++;
    }
    return n;

}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

short stos(string str){
	short ret;
	int ret_i;
	sscanf(str.c_str(), "%d", &ret_i);
	ret = ret_i;
	return ret;
}

short stoc(string str){
	char ret;
	int ret_i;
	sscanf(str.c_str(), "%d", &ret_i);
	ret = ret_i;
	return ret;
}

float stof(string str){
	float ret;
	sscanf(str.c_str(), "%f", &ret);
	return ret;
}

string locknames(string condition){

	if(options->cmd_option_bool("subst_names") == false)
		return condition;

	vector<string> subst = options->cmd_option_vector_str("subst_name");

	for( vector<string>::iterator it = subst.begin(); it != subst.end(); it++ ){

		string substs = *it;
		vector<string> tokens = tokenize(substs, " ");

		if(tokens.size() != 2) assert(0 && "Names cropped");

		string from   = tokens[0];
		string to     = tokens[1];

		myReplace(condition, from, to);

		//printf("locknames_option %s\n", it->c_str());

	}

	return condition;

}

string binary_rep(int n){

	stringstream ret;

	for( int c = 30; c >= 0; c--){
		int k = n >> c;
		if(k & 1)
			ret << 1;
		else 
			ret << 0;
	}

	return ret.str();
}

string hex2dec(string in){

	int a;
	char ret_str[10];
	sscanf(in.c_str(), "%x", &a);
	sprintf(ret_str, "%d", a);

	return string(ret_str);
}


 
uint32_t rc_crc32(uint32_t crc, const char *buf, size_t len) {
	static uint32_t table[256];
	static int have_table = 0;
	uint32_t rem;
	uint8_t octet;
	int i, j;
	const char *p, *q;
 
	/* This check is not thread safe; there is no mutex. */
	if (have_table == 0) {
		/* Calculate CRC table. */
		for (i = 0; i < 256; i++) {
			rem = i;  /* remainder from polynomial division */
			for (j = 0; j < 8; j++) {
				if (rem & 1) {
					rem >>= 1;
					rem ^= 0xedb88320;
				} else
					rem >>= 1;
			}
			table[i] = rem;
		}
		have_table = 1;
	}
 
	crc = ~crc;
	q = buf + len;
	for (p = buf; p < q; p++) {
		octet = *p;  /* Cast to unsigned octet. */
		crc = (crc >> 8) ^ table[(crc & 0xff) ^ octet];
	}
	return ~crc;
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




