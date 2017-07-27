/*
 * =====================================================================================
 * /
 * |     Filename:  goanna_fpr.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/23/2015 11:26:27 AM
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


#include "goanna_fpr.h"

using namespace std;

float goanna_time = 0;
float forest_time = 0;

string close_str(string offset_tree){

	int depth = 0;
	for ( unsigned int i = 0; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0) return offset_tree.substr(0,i+1);
	}

	assert(0 && "Unbalanced tree");

}

// trim from start
static inline std::string ltrim(std::string s) {
        s.erase(s.begin(), std::find_if(s.begin(), s.end(), std::not1(std::ptr_fun<int, int>(std::isspace))));
        return s;
}

// trim from end
static inline std::string rtrim(std::string s) {
        s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
        return s;
}

// trim from both ends
static inline std::string trim(std::string s) {
        return ltrim(rtrim(s));
}

void generate_goanna_file(){

	//printf("generate_goanna_file\n");

	string file = cmd_option_str("file");

	ifstream input(prj_file(file).c_str());
	string line;
	vector<string> output;
	
	while( getline( input, line ) ) {

		output.push_back(line);
	}

	for ( unsigned int i = 0; i < output.size(); i++) {

		
		if(i < output.size()-5 &&
		   output[i+0].find( "__VERIFIER_assert" ) != string::npos &&
		   output[i+1].find( "(!(cond))"         ) != string::npos &&
		   output[i+2].find( "__VERIFIER_error"  ) != string::npos &&
		   output[i+3].find( "}"                 ) != string::npos &&
		   output[i+4].find( "return"            ) != string::npos &&
		   output[i+5].find( "}"                 ) != string::npos
		){
			output[i+0] = "";
			output[i+1] = "";
			output[i+2] = "";
			output[i+3] = "";
			output[i+4] = "";
			output[i+5] = "";
		}


		//myReplace(output[i], "__VERIFIER_assert"                                              , "assert");
		//myReplace(output[i], "extern void __VERIFIER_error() __attribute__ ((__noreturn__));" , "#include <assert.h>"      );
		myReplace(output[i], "extern void __VERIFIER_error() __attribute__ ((__noreturn__));" , "" );
		myReplace(output[i], "__VERIFIER_assert " , "__VERIFIER_assert" );
		myReplace(output[i], "#include \"assert.h\"" , "#define LARGE_INT 1000000" );
		
		line = output[i];
		if(line.find("__VERIFIER_assert") != string::npos){
			size_t it = line.find("__VERIFIER_assert") + strlen("__VERIFIER_assert");
			line = close_str(line.substr(it));
			line = "if(!" + line + ") \"GOANNA_REACHED\";";
		}

		output[i] = line;


	}



	FILE* file_p = fopen(tmp_file("goanna_file.c").c_str(), "w");
	for( vector<string>::iterator it = output.begin(); it != output.end(); it++ ){
		fprintf(file_p, "%s\n", it->c_str());
	}
	fclose(file_p);

	//printf("end generate_goanna_file\n");
	
}


set<pair<string, int> > get_goanna_lines(){
	set<pair<string, int> > ret;

	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	stringstream cmd;
	cmd << "goannacc ";
	cmd << "--timeout-per-phase=0 --timeout-error=42 ";
	cmd << "--smtfpe-observer-limit=300 --smtfpe-iteration-limit=25 ";
	cmd << "--nc --trace --check=REACHABILITY --no-stdchecks ";
	cmd << "--license-server=goanna.ken.nicta.com.au ";
	cmd << "--package-dir=/usr/local/goanna/plugins ";
	cmd << "--debug-detail=smtfpe ";
	cmd << tmp_file("goanna_file.c") << " ";
	cmd << "2>" << tmp_file("goanna_output") << ";";
	cmd << "echo exit_code: $? >> " << tmp_file("goanna_output");

	systm(cmd.str().c_str());

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	goanna_time = 0;
	goanna_time += pong_time.tv_sec - ping_time.tv_sec;
	goanna_time *= 1e9;
	goanna_time += pong_time.tv_nsec - ping_time.tv_nsec;
	goanna_time /= 1e9;


	systm(("cat " + tmp_file("goanna_output") + " | grep REACHABILITY | cut -d':' -f2 > " + tmp_file("goanna_lines")).c_str());


	

	
	ifstream input2(tmp_file("goanna_lines").c_str());
	string line2;
	while( getline( input2, line2 ) ) {
		ret.insert(pair<string, int>("", stoi(line2)));
	}
	ifstream input(tmp_file("goanna_output").c_str());
	string line;
	while( getline( input, line ) ) {
		if(line.substr(0, 10) == "exit_code:" && tokenize(line, ": ")[1] == "42")
			ret.insert(pair<string, int>("", stoi(line)));
	}
	
		

	return ret;
}


string get_goanna_reason(){

	vector<string> errors;

	errors.push_back("FPE loops");
	errors.push_back("Cannot encode assume expression");
	errors.push_back("Goanna parser failed");
	errors.push_back("too many conflicts");

	for( vector<string>::iterator it = errors.begin(); it != errors.end(); it++ ){
		systm(("cat " + tmp_file("goanna_output") + " | grep '" + *it + "' > " + tmp_file("goanna_lines")).c_str());
		ifstream input(tmp_file("goanna_lines").c_str());
		string line;
		if( getline( input, line ) ) {
			return *it;
		}
	}
	

	return "";
}

void goanna_fpr(){

	start_pass("goanna_fpr");

	generate_goanna_file();
	set<pair<string, int> > goanna_lines = get_goanna_lines();

	string forest_reachable_str;
	if(svcomp_get_result() == "TRUE" ) forest_reachable_str = "\e[32m correct   \e[0m";
	if(svcomp_get_result() == "FALSE") forest_reachable_str = "\e[31m incorrect \e[0m";
	if(svcomp_get_result() == "???"  ) forest_reachable_str = "\e[33m ???       \e[0m";

	string desired_result;
	desired_result;
	if(cmd_option_str("file").find("_true-") != string::npos ) desired_result = "TRUE";
	else if(cmd_option_str("file").find("_false-") != string::npos ) desired_result = "FALSE";
	else desired_result = "???";

	if( cmd_option_str("file").find("_true-") != string::npos && cmd_option_str("file").find("_true-") != string::npos ){
		string file_str = cmd_option_str("file");
		if( file_str.find("_false-") < file_str.find("_true-") ){
			desired_result = "FALSE";
		} else if( file_str.find("_true-") < file_str.find("_false-") ){
			desired_result = "TRUE";
		} else {
			assert(0 && "same positions?");
		}

	}













	string filename = cmd_option_str("file");
	if(desired_result == "TRUE" ) filename = "\e[32m " + filename + " \e[0m";
	if(desired_result == "FALSE") filename = "\e[31m " + filename + " \e[0m";
	string lineout = "File: " + filename + " ";
	fill_dots(lineout, 75);

	lineout += "Goanna:";
	lineout += goanna_lines.size()?"\e[31m Warning \e[0m":"\e[32m ..O.K.. \e[0m";
	lineout += "Forest:";
	lineout += forest_reachable_str.c_str();

	{
		forest_time = svcomp_get_time();
		int n = (int)forest_time;
		int h = n/3600;
		int x = n%3600;
		int m = x/60;
		int s = x%60;
		char time[100];
		if( 0 <= s && s <= 20          ) sprintf(time, "\e[32m %02d:%02d:%02d \e[0m", h, m, s);
		if(20 <= s && s <= 40          ) sprintf(time, "\e[33m %02d:%02d:%02d \e[0m", h, m, s);
		if(40 <= s && s <= 59 || m == 1) sprintf(time, "\e[31m %02d:%02d:%02d \e[0m", h, m, s);
		fill_dots(lineout, 115);
		lineout += "forest_time " + string(time);
	}

	{
		int n = (int)goanna_time;
		int h = n/3600;
		int x = n%3600;
		int m = x/60;
		int s = x%60;
		char time[100];
		if( 0 <= s && s <= 20          ) sprintf(time, "\e[32m %02d:%02d:%02d \e[0m", h, m, s);
		if(20 <= s && s <= 40          ) sprintf(time, "\e[33m %02d:%02d:%02d \e[0m", h, m, s);
		if(40 <= s && s <= 59 || m == 1) sprintf(time, "\e[31m %02d:%02d:%02d \e[0m", h, m, s);
		lineout += "goanna_time " + string(time);
	}

	fill_dots(lineout, 160);
	lineout+= get_goanna_reason();

	printf("%s\n", lineout.c_str());
	//printf("filename %s Goanna_warning %s Forest_output %s\n", cmd_option_str("file").c_str(), goanna_lines.size()?"\e[31m Warning \e[0m":"\e[32m ..O.K.. \e[0m", forest_reachable_str.c_str() );

	end_pass("goanna_fpr");
	
}
