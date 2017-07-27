/*
 * =====================================================================================
 * /
 * |     Filename:  utils_frontend.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:12:50 PM
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

#include "utils_frontend.h"


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

void systm( string cmd ){

	stringstream command;

	command << "(";

	command << "cd " << tmp_dir() << "; ";
	
	if( cmd_option_bool("verbose") )
		command << cmd;
	else
		command << "(" << cmd << ") >/dev/null 2>/dev/null";

	command << ")";

	if( cmd_option_bool("verbose") ){
		printf("\e[31m %s \e[0m\n", command.str().c_str() );
		fflush(stdout);
	}

	int ret = system(command.str().c_str() );

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


string prj_file(string file){
	if(file[0] == '/')
		return file;
	else
		return get_project_path() + "/" + file;
}

void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}

bool is_bc(string file){
	int len = file.length();
	string suffix = file.substr(len-3);
	return suffix == ".bc";
}

bool is_bs(string file){
	int len = file.length();
	string suffix = file.substr(len-3);
	return suffix == ".bs";
}

set<string> vtos(vector<string> vect){
	set<string> ret;
	for( vector<string>::iterator it = vect.begin(); it != vect.end(); it++ ){
		ret.insert(*it);
	}

	return ret;
	
}

void printvector( vector<string> v ){


	for( vector<string>::iterator it = v.begin(); it != v.end(); it++ ){
		printf("%s ", it->c_str() );
	} printf("\n");
	

}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

set<string> setintersection(set<string> set_a, set<string> set_b){


	set<string> ret;
	for( set<string>::iterator it = set_a.begin(); it != set_a.end(); it++ ){
		if(set_b.find(*it) != set_b.end()) ret.insert(*it);
	}

	return ret;
	
}

float stof(string str){
	float ret;
	sscanf(str.c_str(), "%f", &ret);
	return ret;
}

