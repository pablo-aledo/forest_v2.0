/*
 * =====================================================================================
 * /
 * |     Filename:  postproc.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/02/2014 08:50:03 AM
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


#include <stdio.h>
#include <vector>
#include <string>
#include <sstream>
#include <string.h>
#include <stdlib.h>
#include <map>
#include <iostream>
#include <fstream>
#include <set>
#include <math.h>
#include <assert.h>

#define SIZE_STR 512


#define COEF_A 3.19
#define COEF_B 0.081
#define COEF_C 129
#define COEF_D 0.002
#define COEF_E -0.0359
#define COEF_F 1.14e4
#define COEF_G 0.583
#define COEF_H 0.0964
#define COEF_I 0.522
#define COEF_J 0.0014
#define COEF_K -0.0831
#define COEF_L 0.345
#define COEF_M 1.44
#define COEF_N 1.16 
#define COEF_O -19.2
#define COEF_P 31.2
#define COEF_Q 284
#define COEF_R 7.04
#define COEF_S 1.22e3
#define COEF_T 0.211
#define COEF_U 6.47
#define COEF_V 0.011 
#define COEF_W 0.0011
#define COEF_X 2.21e-6

using namespace std;

set<string> characteristics_gl;


vector<string> get_list_problems(){
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "ls " << tmp_file("z3_*.smt2") << " | sed 's/\\/tmp\\/forest\\/z3_.*_\\(.*\\)\\.smt2/\\1/g' | sort | uniq";

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret)-1] = 0;
		ret_vector.push_back(ret);
	}
	
	pclose(fp);

	return ret_vector;
	
}



vector<string> get_kind_problems(){
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "ls " << tmp_files("z3_*.smt2") << " | sed 's/\\/tmp\\/forest\\/z3_\\(.*\\)_.*\\.smt2/\\1/g' | sort | uniq";

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret)-1] = 0;
		ret_vector.push_back(ret);
	}
	
	pclose(fp);

	return ret_vector;
	
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


float exec_time(string problem_num, string type){

	string filename = tmp_file("z3_") + type + "_" + problem_num + ".smt2";

	FILE* file = fopen(filename.c_str(), "r");
	if(!file){
		return -1;
	} else {
		fclose(file);
	}

	stringstream command; command << "z3_timed 10 " << filename << " > " << tmp_file("z3_output");


	struct timespec ping_time;
	struct timespec pong_time;

	clock_gettime(CLOCK_MONOTONIC, &ping_time);
	system(command.str().c_str());
	clock_gettime(CLOCK_MONOTONIC, &pong_time);

	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e6;


	ifstream input(tmp_file("z3_output").c_str());
	string line; vector<string> lines;
	while( getline( input, line ) ) {
		lines.push_back(line);
	}
	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		if(it->find("error") != string::npos && lines[0] != "unsat") return -1;
	}
	
	
	

	
	

	return spent_time;
}


string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

string ftos(float i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}



float get_avg_depth(vector<string> assertions, string operand){

	vector<int> depths;

	for( vector<string>::iterator it = assertions.begin(); it != assertions.end(); it++ ){
		string assertion = *it;

		//printf("assertion %s\n", assertion.c_str());

		int depth = 0;
		for ( unsigned int i = 0; i < assertion.length() - ( operand.length()+2 ); i++) {
			string substr_1 = assertion.substr(i,1);
			string substr_2 = assertion.substr(i,2+operand.length());

			//printf("substr_1 %s substr_2 %s\n", substr_1.c_str(), substr_2.c_str());

			if(substr_1 == "(") depth++;
			if(substr_1 == ")") depth--;
			if(substr_2 == "(" + operand + " "){
				depths.push_back(depth);
			}

		}

		//for( vector<int>::iterator it = depths.begin(); it != depths.end(); it++ ){
			//printf("%d ", *it );
		//}
		//printf("\n");
		
	}


	if(!depths.size()) return 0;

	float avg = 0;
	for( vector<int>::iterator it = depths.begin(); it != depths.end(); it++ ){
		avg += *it;
	}
	avg /= depths.size();

	return avg;
	

}


float avg(vector<int> in){

	if(!in.size()) return 0;

	float avg = 0;
	for( vector<int>::iterator it = in.begin(); it != in.end(); it++ ){
		avg += *it;
	}
	avg /= in.size();

	return avg;
	

}


vector<int> get_depths(vector<string> assertions, string operand){

	vector<int> depths;

	for( vector<string>::iterator it = assertions.begin(); it != assertions.end(); it++ ){
		string assertion = *it;

		//printf("assertion %s\n", assertion.c_str());

		int depth = 0;
		for ( unsigned int i = 0; i < assertion.length() - ( operand.length()+2 ); i++) {
			string substr_1 = assertion.substr(i,1);
			string substr_2 = assertion.substr(i,2+operand.length());

			//printf("substr_1 %s substr_2 %s\n", substr_1.c_str(), substr_2.c_str());

			if(substr_1 == "(") depth++;
			if(substr_1 == ")") depth--;
			if(substr_2 == "(" + operand + " "){
				depths.push_back(depth);
			}

		}

		//for( vector<int>::iterator it = depths.begin(); it != depths.end(); it++ ){
			//printf("%d ", *it );
		//}
		//printf("\n");
		
	}


	return depths;

}

vector<string> get_assertions(vector<string> lines){

	vector<string> ret;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		string line = *it;
		if(line.substr(0,8) == "(assert "){
			ret.push_back(line);
		}
	}

	return ret;
}

vector<string> get_variables(vector<string> lines){

	vector<string> ret;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		string line = *it;
		if(line.substr(0,13) == "(declare-fun "){
			ret.push_back(line);
		}
	}

	return ret;
}

int max(vector<vector<int> > input){

	int max = -1;

	for( vector<vector<int> >::iterator it = input.begin(); it != input.end(); it++ ){
		vector<int> vec = *it;
		for( vector<int>::iterator it2 = vec.begin(); it2 != vec.end(); it2++ ){
			int val = *it2;

			if(val > max) max = val;
		}
		
	}

	return max;
	
}

map<string, string> get_characteristics(string problem_num){

	map<string, string> ret;

	FILE *fp;
	stringstream command;
	char cmd_ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "cat " << tmp_file("z3_*_") << problem_num << ".smt2";
	command << " | grep '^;' | grep -v 'free'";

	fp = popen(command.str().c_str(), "r");
	
	while (fgets(cmd_ret,SIZE_STR, fp) != NULL){
		cmd_ret[strlen(cmd_ret)-1] = 0;
		ret_vector.push_back(cmd_ret);
	}
	
	pclose(fp);
	
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, " ");
		characteristics_gl.insert(tokens[1]);
		ret[tokens[1]] = tokens[2];
	}

	return ret;
}

typedef struct Problem {
	string problem_num;
	map<string, string> characteristics;
	map<string, float> times;
} Problem;

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

int stof(string str){
	float ret;
	sscanf(str.c_str(), "%f", &ret);
	return ret;
}

string problem_type(Problem problem){

	string type;
	bool mixedint     = problem.times.find("mixedint")      != problem.times.end() && problem.times["mixedint"    ] > 0;
	bool mixedbblast  = problem.times.find("mixedbblast")   != problem.times.end() && problem.times["mixedbblast" ] > 0;
	bool linear       = problem.times.find("linear")        != problem.times.end() && problem.times["linear"      ] > 0;
	bool linearbblast = problem.times.find("linearbblast")  != problem.times.end() && problem.times["linearbblast"] > 0;
	bool poly         = problem.times.find("poly")          != problem.times.end() && problem.times["poly"        ] > 0;

	if( mixedint && mixedbblast && !linear )
		type = "mixed";
	else if( linear && linearbblast )
		type = "linear";
	else if( poly && !linear )
		type = "poly";
	else
		type = "generic";


	return type;
}

#define INFTY 1000.0

string get_heuristics(Problem problem){

	float ass, var, time_a1, time_b3, time_a2, lin_var_i, lin_var_b, time_e1, time_e2, bv_var, n_bits, bool_words, bits, e2, e1;
	string type = problem_type(problem);
	if(type == ""){ return "unknown"; }

	if(type == "linear"){

		ass  = stof(problem.characteristics["ASSERTIONS"]);
		var  = stof(problem.characteristics["N_TERM_MAX"]);
		bits = stof(problem.characteristics["MAX_BITS"]);

		if(ass < var){
			return "h_linearbblast";
		} else {
			float a2 = COEF_I*ass+COEF_J*ass*var*var*var+COEF_K*var*ass;
			float a1 = bits*exp(COEF_L*ass);

			if(a2 < a1) return "h_linearint";
			else return "h_linearbblast";
		}


	}

	if(type == "mixed"){
		// e2
		ass = stof(problem.characteristics["ASSERTIONS"]);
		lin_var_i = stof(problem.characteristics["N_TERM_MAX_B"]);
		lin_var_b = stof(problem.characteristics["N_TERM_MAX_B"]);
		bv_var = stof(problem.characteristics["BOOL_WORDS"]);
		n_bits = stof(problem.characteristics["MAX_BITS"]);

		if(ass < lin_var_i){
			return "h_mixedbblast";
		} else {

			e1 = COEF_P*lin_var_b*ass+n_bits*ass+COEF_O*ass;
			e2 = COEF_M*lin_var_i+n_bits*ass+COEF_Q+COEF_R*ass;

			if(e1 < e2) return "h_mixedbblast";
			else return "h_mixedint";
			
		}

	}

	if(type == "generic"){
		return "h_realint";
	}

	assert(0 && "Unknown type");

}

string get_best(Problem problem){



	string type = problem_type(problem);
	if(type == ""){ return "unknown "; }

	if(type == "mixed"){
		float time_mixedint    = problem.times["mixedint"];
		float time_mixedbblast = problem.times["mixedbblast"];
		if(time_mixedint < time_mixedbblast)
			return "b_mixedint";
		else
			return "b_mixedbblast";


		
	}

	if(type == "linear"){
		float time_linearint    = problem.times["linear"];
		float time_linearbblast = problem.times["linearbblast"];
		if(time_linearint < time_linearbblast)
			return "b_linearint";
		else
			return "b_linearbblast";

	}

	if(type == "generic"){
		float time_linearint    = problem.times["bitvector"];
		float time_linearbblast = problem.times["realint"];
		if(time_linearint < time_linearbblast)
			return "b_bitvector";
		else
			return "b_realint";
	}


	assert( 0 && "Unknown type");

}


void output(vector<Problem> problems){

	printf("problem_num ");

	for( set<string>::iterator it = characteristics_gl.begin(); it != characteristics_gl.end(); it++ ){
		printf("%s ", it->c_str());
	}
	vector<Problem>::iterator it = problems.begin();
	for( map<string,float>::iterator it2 = it->times.begin(); it2 != it->times.end(); it2++ ){
		printf("%s ", it2->first.c_str());
	}
	printf("\n");


	int hits = 0;
	map<string, int> types;
	for( vector<Problem>::iterator it = problems.begin(); it != problems.end(); it++ ){

		printf("%s ", it->problem_num.c_str());

		map<string, string> characteristics = it->characteristics;
		for( set<string>::iterator it2 = characteristics_gl.begin(); it2 != characteristics_gl.end(); it2++ ){
			if(characteristics.find(*it2) != characteristics.end())
				printf("%s ", it->characteristics[*it2].c_str());
			else
				printf("- ");
		}

		map<string, float> times = it->times;
		for( map<string,float>::iterator it2 = times.begin(); it2 != times.end(); it2++ ){
			if(it2->second == -1)
				printf("- ");
			else
				printf("%f ", it2->second);
		}

		printf("%s ", get_heuristics(*it).c_str());
		printf("%s ", get_best(*it).c_str());
		if(get_heuristics(*it).substr(1) != get_best(*it).substr(1)) printf(" <<< ");
		printf("\n");

		if(get_heuristics(*it).substr(1) == get_best(*it).substr(1))
			hits++;
		types[problem_type(*it)]++;
		
	}
	
	printf("hits %d\n", hits);

	for( map<string,int>::iterator it = types.begin(); it != types.end(); it++ ){
		printf("%s %d\n", it->first.c_str(), it->second);
	}
	
	printf("total %d\n", problems.size());

	printf("hit_rate %.3f\n", (float)(hits)/(float)(problems.size()));
	
	
}

int main(int argc, const char *argv[])
{

	vector<string> list_problems = get_list_problems();
	vector<string> kind_problems = get_kind_problems();
	vector<Problem> problems;
	map<string, float> times;

	for( vector<string>::iterator it = list_problems.begin(); it != list_problems.end(); it++ ){
		string problem_num = *it;

		for( vector<string>::iterator it2 = kind_problems.begin(); it2 != kind_problems.end(); it2++ ){
			float time = exec_time(problem_num, *it2);
			times[*it2] = time;
		}

		map<string, string> characteristics = get_characteristics(problem_num);

		Problem problem = {problem_num, characteristics, times};
		problems.push_back(problem);
	}

	output(problems);
	
	return 0;
}
