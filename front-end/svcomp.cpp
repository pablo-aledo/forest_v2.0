/*
 * =====================================================================================
 * /
 * |     Filename:  svcomp.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 05:33:22 PM
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

#include "svcomp.h"

bool is_parseable(){

	stringstream cmd;
	string llvm_path = cmd_option_str("llvm_path");

	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -check_parseable < file.bc >/dev/null";
	systm(cmd.str());

	ifstream input(tmp_file("parseable").c_str());
	string line;
	
	getline( input, line );

	if(line != "true")
		systm("touch not-parseable");

	return line=="true";

}

bool is_compilable(){

	stringstream cmd;
	string llvm_path = cmd_option_str("llvm_path");

	cmd.str("");
	cmd << "llvm-gcc -c file.c > compilable 2> compilable";
	systm(cmd.str());


	ifstream input(tmp_file("compilable").c_str());
	string line;
	
	while( getline( input, line ) ) {
		if(line.find("error") != string::npos){
			systm("touch not-compilable");
			return false;
		}
	}

	return true;

}

string svcomp_global_result;
float spent_time = 0;

void svcomp(){
	start_pass("svcomp");

	if(cmd_option_bool("visualize_coverage")) system("coverage_viewer &");      // shows coverage in a graphical way

	string result = "???";

	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	bool exec = true;


	//if( !is_parseable() ){
		//exec = false;
		//result = "???";
	//}

	if(!is_compilable()){
		exec = false;
		result = "???";
	}


	set_option("follow_path", "true");
	set_option("single_step", "true");

	set<PathAndConds> frontier;

	load_heuristics();

	//if(exec && !get_heuristics().size())
		//exec = false;

	//exec = false;
	if(cmd_option_bool("force_run"))
		exec = true;

	if( cmd_option_bool("check_without_instrumentation") && check_without_instrumentation() == "FALSE" ){
		//printf("checked_without_instrumentation\n");
		exec = false;
		result = "FALSE";
	}
	
	if(exec)
	do {
		PathAndConds first;
		if(frontier.size()){
			first = *(frontier.begin());
			frontier.erase(frontier.begin());
		}

		set_option("path", first.path);
		set_option("file_initializations", first.file_initializations);

		options_to_file();

		db_command("delete from frontend;");
		db_command("delete from results;");
		db_command("delete from last_bb;");
		db_command("delete from variables;");

		////Run resulting file
		//if(pid_t pid = fork()){

			//struct timespec ping_time_2;
			//clock_gettime(CLOCK_MONOTONIC, &ping_time_2);
			//printf("eo\n");

			//while(true){

				//struct timespec pong_time_2;
				//clock_gettime(CLOCK_MONOTONIC, &pong_time_2);

				//float spent_time = 0;
				//spent_time += pong_time_2.tv_sec - ping_time_2.tv_sec;
				//spent_time *= 1e9;
				//spent_time += pong_time_2.tv_nsec - ping_time_2.tv_nsec;
				//spent_time /= 1e9;

				//int status;
				//pid_t result = waitpid(pid, &status, WNOHANG);
				//if( spent_time > 10.0){
					//kill(pid, 9);
					//system("killall final");
					//break;
				//}

				//if(result){
					//break;
				//}

				//printf("hola %f\n", spent_time);

				//usleep(1000000);
			//}
		//} else {
			//stringstream cmd;
			//cmd << "./" << cmd_option_str("output_file");
			//systm(cmd.str().c_str());
			//exit(0);
		//}
		//Run resulting file
		stringstream cmd;
		cmd << "./" << cmd_option_str("output_file");
		systm(cmd.str().c_str());

		add_paths(frontier);
		if(frontier.size() && frontier.begin()->path.length() > cmd_option_int("max_depth")){
			if(cmd_option_bool("complete")){
				result = "???";
				break;
			} else {
				frontier.erase(frontier.begin());
			}
		}
			
		//print_frontier_simple(frontier);
		//print_frontier_simple_2(frontier);
		if(cmd_option_bool("show_frontier")){
			print_frontier(frontier);
			printf("last_bb %s\n", get_last_bb().c_str());
		}

		clock_gettime(CLOCK_MONOTONIC, &pong_time);
		spent_time = 0;
		spent_time += pong_time.tv_sec - ping_time.tv_sec;
		spent_time *= 1e9;
		spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
		spent_time /= 1e9;

		if(get_overflow()){
			//printf("overflow\n");
			result = "FALSE";
			break;
		}

		if(get_doublefree()){
			//printf("double_free\n");
			result = "FALSE";
			break;
		}


		if(spent_time > cmd_option_int("max_time_min")*60){
			if(cmd_option_bool("complete")){
				result = "???";
			} else {
				result = "TRUE";
			}

			break;
		}

		if(get_last_bb() == cmd_option_str("target_node")){
			//printf("targetnode\n");
			result = "FALSE";
			break;
		}

		if(get_last_bb().find("ERROR") != string::npos){
			//printf("targetnode\n");
			result = "FALSE";
			break;
		}



		if(!frontier.size()){
			result = "TRUE";
			break;
		}

	} while(frontier.size());

	//printf("%s\n", result.c_str());
	

	string lineout = cmd_option_str("file") + " ";
	fill_dots(lineout, 75);

	string desired_result;
	desired_result;
	if(cmd_option_str("file").find("_true-") != string::npos ) desired_result = "TRUE";
	else if(cmd_option_str("file").find("_false-") != string::npos ) desired_result = "FALSE";
	else if(cmd_option_str("file").find("_unsafe") != string::npos ) desired_result = "FALSE";
	else if(cmd_option_str("file").find("_usafe") != string::npos ) desired_result = "FALSE";
	else if(cmd_option_str("file").find("-valid-") != string::npos ) desired_result = "TRUE";
	else if(cmd_option_str("file").find("_false.") != string::npos ) desired_result = "FALSE";
	else if(cmd_option_str("file").find("_true.") != string::npos ) desired_result = "TRUE";
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



	lineout += " R:" + string(result=="TRUE"?"\e[32mTRUE\e[0m":result=="???"?"\e[33m???\e[0m":"\e[31mFALSE\e[0m") + " ";
	fill_dots(lineout, 90);

	lineout += " D:" + string(desired_result=="TRUE"?"\e[32mTRUE\e[0m":desired_result=="FALSE"?"\e[31mFALSE\e[0m":"\e[33m???\e[0m") + " ";
	fill_dots(lineout, 100);

	int score;
	string score_s;
	if( desired_result == "TRUE" && result == "TRUE"){
		score = 2;
	}
	if( desired_result == "FALSE" && result == "FALSE"){
		score = 1;
	}
	if( desired_result == "TRUE" && result == "FALSE"){
		score = -6;
	}
	if( desired_result == "FALSE" && result == "TRUE"){
		score = -12;
	}
	if( result == "???" ){
		score = 0;
	}
	if(desired_result == "???"){
		score = 0;
	}

	if(score == 0){
		score_s = string("\e[33m") + itos(score) + string("\e[0m");
	} else if(score < 0){
		score_s = string("\e[31m") + itos(score) + string("\e[0m");
	} else {
		score_s = string("\e[32m +") + itos(score) + string("\e[0m");
	}

	lineout += " " + score_s + " ";


	if( result == "FALSE"){
		generate_witness();
		if(cmd_option_bool("check_witness")){
			if( check_witness()){
				lineout += "\e[32m Witness OK \e[0m";
			} else {
				lineout += "\e[31m Witness NOK \e[0m";
			}
		}
	}


	int n = (int)spent_time;
	int h = n/3600;
	int x = n%3600;
	int m = x/60;
	int s = x%60;

	char time[100];
	if(0 <= m && m <=  1) sprintf(time, "\e[32m %02d:%02d:%02d \e[0m", h, m, s);
	if(1 <= m && m <=  5) sprintf(time, "\e[33m %02d:%02d:%02d \e[0m", h, m, s);
	if(5 <= m && m <= 15) sprintf(time, "\e[31m %02d:%02d:%02d \e[0m", h, m, s);


	fill_dots(lineout, 130);
	lineout += string(time);

	if(cmd_option_bool("svcomp_only_output")){

		string result2;
		if(result == "FALSE")                     result2 = "FALSE_REACH";
		if(result == "FALSE" && get_overflow())   result2 = "FALSE_DEREF";
		if(result == "FALSE" && get_doublefree()) result2 = "FALSE_FREE";
		if(result == "TRUE")                      result2 = "TRUE_PROP";
		if(result == "???")                       result2 = "RESULT_UNKNOWN";

		printf("%s\n", result2.c_str());
	} else {
		if(!cmd_option_bool("svcomp_silent")) printf("* Testing %s\n", lineout.c_str() );
	}

	svcomp_global_result = result;

	end_pass("svcomp");

	//printf("result %s\n", result.c_str());

}

string svcomp_get_result(){
	return svcomp_global_result;
}


float svcomp_get_time(){
	return spent_time;
}

string check_without_instrumentation(){

	stringstream cmd;

	// Joins all c files in one
	cmd.str("");
	cmd << "cat ";
	vector<string> files = cmd_option_string_vector("file");
	for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
		cmd << prj_file(*it) << " ";
	}
	cmd << "> " << tmp_file("file.c");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "echo '#include <stdio.h>' >> " << tmp_file("file.c");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "echo 'void __VERIFIER_error(){printf(\"ERROR\\\\n\");}' >> " << tmp_file("file.c");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "rm -f a.out checkerror";
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "gcc file.c 2> /dev/null";
	systm(cmd.str().c_str());

	if(pid_t pid = fork()){
		
		struct timespec ping_time;
		clock_gettime(CLOCK_MONOTONIC, &ping_time);

		while(true){

			struct timespec pong_time;
			clock_gettime(CLOCK_MONOTONIC, &pong_time);

			float spent_time = 0;
			spent_time += pong_time.tv_sec - ping_time.tv_sec;
			spent_time *= 1e9;
			spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
			spent_time /= 1e9;

			int status;
			pid_t result = waitpid(pid, &status, WNOHANG);
			if( spent_time > 15 ){
				kill(pid, 9);
				system("killall a.out 2>/dev/null");
				break;
			}

			if(result){
				break;
			}

			usleep(1000);
		}
	} else {
		cmd.str("");
		cmd << "./a.out | grep ERROR > checkerror";
		systm(cmd.str().c_str());
		exit(0);
	}

	ifstream input(tmp_file("checkerror").c_str());
	string line;
	
	if( getline( input, line ) ) {
		//printf("ERROR\n");
		return "FALSE";
	} else {
		//printf("NOERROR\n");
		return "UNKNOWN";
	}
	


	exit(0);



}

bool get_overflow(){
	stringstream command;
	command << "echo 'select * from exceptions;' | sqlite3 database.db > " << tmp_file("overflow");
	systm(command.str().c_str());
	

	ifstream input(tmp_file("overflow").c_str());
	string line;
	
	input >> line;

	return line.size();
}

bool get_doublefree(){
	stringstream command;
	command << "echo 'select * from exceptions;' | sqlite3 database.db > " << tmp_file("overflow");
	systm(command.str().c_str());
	

	ifstream input(tmp_file("overflow").c_str());
	string line;
	
	input >> line;

	return line.size();
}

void fill_dots(string& line, int length){
	string line2 = line;
	myReplace(line2, "\e[31m", "");
	myReplace(line2, "\e[32m", "");
	myReplace(line2, "\e[33m", "");
	myReplace(line2, "\e[0m" , "");

	while(line2.length() < length){
		line  += ".";
		line2 += ".";
	}
}

map<string, int> read_position_to_token(){
	map<string, int> ret;
	ifstream input(tmp_file("analysis_bc").c_str());
	string line;
	
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, " ");
		ret[tokens[0]] = stoi(tokens[1]);
	}

	return ret;
	
}

vector<string> get_trace_positions(){

	stringstream cmd;

	cmd.str();
	cmd << "echo \'select * from trace;\'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " > " << tmp_file("tracep_out");


	systm(cmd.str());

	ifstream input(tmp_file("tracep_out").c_str());
	string line;

	vector<string> ret;
	
	if( getline( input, line ) ) {
		ret = tokenize(line, ",");
	}

	return ret;
	


}

void output_witness(vector<int> tokens){


	FILE* file = fopen( prj_file(cmd_option_str("witness")).c_str(), "w");

	fprintf(file, "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n");
	fprintf(file, "<graphml xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xmlns=\"http://graphml.graphdrawing.org/xmlns\">\n");
	fprintf(file, "<graph edgedefault=\"directed\">\n");

	fprintf(file, "<node id=\"A1\"><data key=\"entry\">true</data> </node>\n");
	for ( unsigned int i = 2; i < tokens.size()+1; i++) {
		fprintf(file, "   <node id=\"A%d\"/>\n", i);
	}
	fprintf(file, "   <node id=\"A%d\"> <data key=\"sink\">true</data><data key=\"violation\">true</data></node>\n", tokens.size()+1);



	int i = 1;
	for( vector<int>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
		fprintf(file, "   <edge source=\"A%d\" target=\"A%d\"> <data key=\"tokens\">%d</data> </edge>\n", i, i+1, *it);
		i++;
	}


	fprintf(file, "</graph>\n");
	fprintf(file, "</graphml>\n");

	fclose(file);
	
}

void output_empty_witness(){


	FILE* file = fopen( prj_file(cmd_option_str("witness")).c_str(), "w");

	fprintf(file, "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n");
	fprintf(file, "<graphml xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xmlns=\"http://graphml.graphdrawing.org/xmlns\">\n");
	fprintf(file, "<graph edgedefault=\"directed\">\n");
	fprintf(file, "   <node id=\"A1\"><data key=\"entry\">true</data> </node>\n");
	fprintf(file, "   <node id=\"A2\"> <data key=\"sink\">true</data> <data key=\"violation\">true</data></node>\n");
	fprintf(file, "   <edge source=\"A1\" target=\"A2\"> <data key=\"tokens\">0</data> </edge>\n");
	fprintf(file, "</graph>\n");
	fprintf(file, "</graphml>\n");

	fclose(file);
	
}

void generate_witness(){

	stringstream cmd;
	string llvm_path = cmd_option_str("llvm_path");

	cmd.str("");
	cmd << "rm -f " << tmp_file("file_tokenize.c") << " " << tmp_file("file_tokenize_2.c") << " " << tmp_file("tokenized.c") << ";";
	cmd << "cp " << prj_file(cmd_option_str("file")) << " " << tmp_file("file_tokenize_2.c") << ";";
	//cmd << "gcc -E " << tmp_file("file_tokenize.c") << " -o " << tmp_file("file_tokenize_2.c") << ";";
	//cmd << "cp " << tmp_file("file_tokenize.c") << " " << tmp_file("file_tokenize_2.c") << ";";
	cmd << "tokenizer " <<  tmp_file("file_tokenize_2.c") << " > " << tmp_file("tokenized.c");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "llvm-gcc -c -g --emit-llvm -o tokenized.bc " << tmp_file("tokenized.c");
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestBcAnalyze.so -bcanalyze < tokenized.bc > tokenized-2.bc";
	systm(cmd.str().c_str());

	map<string, int> map_position_to_token = read_position_to_token();
	vector<string> trace_positions = get_trace_positions();
	vector<int> tokens_trace;

	for( vector<string>::iterator it = trace_positions.begin(); it != trace_positions.end(); it++ ){
		//assert(map_position_to_token.find(*it) != map_position_to_token.end() && "position unknown");
		if(map_position_to_token.find(*it) == map_position_to_token.end()){
			continue;
			//output_empty_witness();
			//return;
		}
		tokens_trace.push_back( map_position_to_token[*it] );
	}

	if( !trace_positions.size() || !map_position_to_token.size() )	
		output_empty_witness();
	else
		output_witness(tokens_trace);

	
}

bool check_witness(){
	stringstream cmd;
	string llvm_path = cmd_option_str("llvm_path");

	cmd.str("");
	cmd << "cp " << prj_file(cmd_option_str("file")) << " " << tmp_file("file_check_witness_2.c") << ";";
	//cmd << "gcc -E " << tmp_file("file_check_witness.c") << " -o " << tmp_file("file_check_witness_2.c") << ";";
	cmd << "rm " << tmp_file("witness_ok") << ";";
	//cmd << "cd /home/mint/CPAchecker-1.3.4-unix/;";
	cmd << "cd " << cmd_option_str("cpachecker_path") << ";";

	// cmd << "scripts/cpa.sh -explicitAnalysis-NoRefiner -setprop analysis.checkCounterexamples=false -setprop cpa.value.merge=SEP";
	// cmd << " -setprop cfa.useMultiEdges=false -setprop parser.transformTokensToLines=true -spec " << get_project_path() << "/" << cmd_option_str("witness");
	// cmd << " -spec ALL.prp " << tmp_file("file_check_witness_2.c");
	// cmd << " 2>&1 | grep TRUE > " << tmp_file("witness_ok");

	//./scripts/cpa.sh -witness-check \
	//-spec witness-to-validate.graphml \
	//-spec PropertyERROR.prp \
	//test.c

	cmd << "scripts/cpa.sh -witness-check -spec " << get_project_path() << "/" << cmd_option_str("witness");
	cmd << " -spec ALL.prp " << tmp_file("file_check_witness_2.c");
	cmd << " 2>&1 | grep FALSE > " << tmp_file("witness_ok");

	//printf("Validation_command: (%s)\n", cmd.str().c_str());
	systm(cmd.str());

	ifstream input(tmp_file("witness_ok").c_str());
	string line;
	
	if( getline( input, line ) ) {
		return 1;
	} else {
		return 0;
	}
}

