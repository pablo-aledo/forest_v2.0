/*
 * =====================================================================================
 * /
 * |     Filename:  klee.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:40:58 PM
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

#include "klee.h"

#define SIZE_STR 1024

void do_klee(){

	start_pass("klee");

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc_klee();

	// run klee
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;

	//command << "(cd " << cmd_option_str("tmp_dir") << "; klee --emit-all-errors file.bc 2>&1)";
	command << "(cd " << tmp_dir() << "; klee -max-time=10 --emit-all-errors file.bc 2>&1)";

	cmd_option_bool("verbose") && printf("\e[31m %s \e[0m\n", command.str().c_str());
	

	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	fp = popen(command.str().c_str(), "r");
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	pclose(fp);

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e9;
	int time_ms_int = (int)(spent_time*1000.0);
	//int time_ms_int = (int)(spent_time);

	
	// Number of executed paths
	int completed_paths;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		if( it->find("completed paths") != string::npos ){
			completed_paths = stoi(it->substr( it->find("=")+1 ));
		}
	}

	// Save values in the database
	db_command( "create table klee( time_ms Integer, paths Integer );" );
	cmd.str("");
	cmd << "insert into klee values('" << time_ms_int << "','" << completed_paths << "');";
	db_command(cmd.str());



	cmd.str("");
	cmd << "ktest-tool --write-ints klee-last/test*.ktest | tee output_klee";
	systm(cmd.str());




	end_pass("klee");

}

void klee_coverage(){

	//start_pass("klee_coverage");

	measure_coverage();
	do_klee();
	tests_from_klee();


	gen_final_for_measurement();
	set_option("measurement", "true");
	options_to_file();
	string output_file = cmd_option_str("output_file");
	stringstream cmd;
	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());


	systm("echo 'select * from measurements;' | sqlite3 database.db > coverage_measurements;");

	
	ifstream input(tmp_file("coverage_measurements").c_str());
	string line;
	vector<string> lines;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}


	int coverage_forest = stoi(tokenize(lines[lines.size()-3], "() ")[1]);
	int coverage_klee   = stoi(tokenize(lines[lines.size()-1], "() ")[1]);
	
	
	char color[] = "\e[0m";
	
	if(coverage_forest < coverage_klee)
		strcpy(color, "\e[31m"); // Red
	else if(coverage_forest > coverage_klee)
		strcpy(color, "\e[32m"); // Green
	else
		strcpy(color, "\e[33m"); // Yellow



	printf("%s coverage_forest %d coverage_klee %d \e[0m\n", color,coverage_forest,coverage_klee);


	show_coverage();

	//end_pass("klee_coverage");
}

void make_initial_bc_klee(){

	stringstream cmd;

	// Join all c files into one
	cmd.str("");
	cmd << "cat ";
	vector<string> files = cmd_option_string_vector("file");
	for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
		cmd << prj_file(*it) << " ";
	}
	cmd << "> " << tmp_file("file.cpp");
	systm(cmd.str().c_str());



	string base_path = cmd_option_str("base_path");


	// Compile to BC
	cmd.str("");
	cmd << "llvm-g++ -O0 --emit-llvm -D KLEE -c file.cpp -o file.bc";
	systm(cmd.str().c_str());

}

void tests_from_klee(){

	ifstream input( tmp_file("output_klee").c_str() );
	string line;
	vector<string> lines;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}

	set<string> free_variables;
	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		if( it->find(":") != string::npos ){
			vector<string> tokens = tokenize(*it, ":");
			if(tokens[1] == " name"){
				free_variables.insert(tokenize(*it, "'")[1]);
			}
		}
	}

	
	map<string, int> free_variables_size;
	//for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
	for ( unsigned int i = 0; i < lines.size(); i++) {
		if( lines[i].find(":") != string::npos ){
			vector<string> tokens = tokenize(lines[i], ":");
			if(tokens[1] == " name"){
				string name = tokenize(lines[i], "'")[1];
				int size = stoi( tokenize(lines[i+1],":")[2] );
				free_variables_size[name] = size;
			}
		}
	}
	
	//FILE* file = fopen(tmp_file("free_variables").c_str(), "w");
	//for( map<string,int>::iterator it = free_variables_size.begin(); it != free_variables_size.end(); it++ ){
		//string name = it->first;
		//int size = it->second;
		//string type;
		//if(size == 4)
			//type = "Int32";
		//fprintf(file, "%s %s\n",type.c_str(), name.c_str());
	//}
	//fclose(file);
	
	set<pair<string, string> > free_variables_split;
	ifstream input2(tmp_file("free_variables").c_str());
	while( getline( input2, line ) ) {
		vector<string> tokens = tokenize(line, " ");
		free_variables_split.insert( pair<string, string>(tokens[2], tokens[0] + " " + tokens[1]) );
	}
	
	FILE* file = fopen(tmp_file("free_variables").c_str(), "w");
	for( set<pair<string, string> >::iterator it = free_variables_split.begin(); it != free_variables_split.end(); it++ ){
		string name = it->first;
		string posandtype = it->second;
		fprintf(file, "%s %s\n", posandtype.c_str(), name.c_str());
	}
	fclose(file);
	
	

	
	set<string> names = free_variables;
	map< int, map<string, string> > values;
	int n = 0;

	for ( unsigned int i = 0; i < lines.size(); i++) {
		string line = lines[i];
		if(line == "()") n++;

		if( lines[i].find(":") != string::npos ){
			vector<string> tokens = tokenize(lines[i], ":");
			if(tokens[1] == " name"){
				string name = tokenize(lines[i], "'")[1];
				string data = tokenize(lines[i+2],": ")[3];
				values[n][name] = data;
			}
		}
	}

	set<vector<string> > vectors = pivot(values, names);




	vector<string> output_file;
	for( set<vector<string> >::iterator it = vectors.begin(); it != vectors.end(); it++ ){
		vector<string> vect = *it;

		string line;
		for( vector<string>::iterator it2 = vect.begin(); it2 != vect.end(); it2++ ){
			line += *it2 + " ";
		}
		
		output_file.push_back(line);
	}


	string filename;

	filename = tmp_file("vectors");

	FILE* file2 = fopen( filename.c_str(), "w");
	for( vector<string>::iterator it = output_file.begin(); it != output_file.end(); it++ ){
		fprintf(file2, "%s\n", it->c_str());
	}
	fclose(file2);

}

void compare_klee(){

	start_pass("compare_klee");


	int paths_klee;
	int paths_forest;
	int time_klee;
	int time_forest;
	int coverage_forest;
	int coverage_klee;

	stringstream command;
	
	{
		command.str("");
		command << "cd " << tmp_dir() << "; echo 'select paths from klee;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &paths_klee);
		pclose(fp);
	}
	
	{
		command.str("");
		command << "cd " << tmp_dir() << "; echo 'select count(distinct vector_id) from minimal_vectors;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &paths_forest);
		pclose(fp);
	}


	{
		command.str("");
		command << "cd " << tmp_dir() << "; echo 'select time_ms from klee order by rowid desc limit 1;' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &time_klee);
		pclose(fp);
	}

	{
		command.str("");
		command << "cd " << tmp_dir() << "; echo 'select value from measurements where key=\"time_ms\";' | sqlite3 database.db";
		FILE *fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d", &time_forest);
		pclose(fp);
	}



	{

		measure_coverage();
		do_klee();
		tests_from_klee();
	
	
		gen_final_for_measurement();
		set_option("measurement", "true");
		options_to_file();
		string output_file = cmd_option_str("output_file");
		stringstream cmd;
		cmd.str("");
		cmd << "./" << output_file;
		systm(cmd.str().c_str());
	
	
		systm("echo 'select * from measurements;' | sqlite3 database.db > coverage_measurements;");
	
		
		ifstream input(tmp_file("coverage_measurements").c_str());
		string line;
		vector<string> lines;
		
		while( getline( input, line ) ) {
			lines.push_back(line);
		}
	
	
		coverage_forest = stoi(tokenize(lines[lines.size()-3], "() ")[1]);
		coverage_klee   = stoi(tokenize(lines[lines.size()-1], "() ")[1]);
		
		
	}

	string explanation = cmd_option_str("explanation") + " ";
	while( explanation.length() < 50 )
		explanation = explanation + ".";
	printf("* Comparing %s", explanation.c_str() );

	char color_p[] = "\e[0m";
	char color_t[] = "\e[0m";
	char color_c[] = "\e[0m";
	
	if(paths_forest < paths_klee)
		strcpy(color_p, "\e[31m"); // Red
	else if(paths_forest > paths_klee)
		strcpy(color_p, "\e[32m"); // Green
	else
		strcpy(color_p, "\e[33m"); // Yellow

	if(time_forest > time_klee)
		strcpy(color_t, "\e[31m"); // Red
	else if(time_forest < time_klee)
		strcpy(color_t, "\e[32m"); // Green
	else
		strcpy(color_t, "\e[33m"); // Yellow


	if(coverage_forest < coverage_klee)
		strcpy(color_c, "\e[31m"); // Red
	else if(coverage_forest > coverage_klee)
		strcpy(color_c, "\e[32m"); // Green
	else
		strcpy(color_c, "\e[33m"); // Yellow



	printf("%s Paths_klee %-3d Paths_forest %-3d\e[0m %s Time_klee %-3d Time_forest %-3d %s Coverage_forest %-3d Coverage_klee %-3d\e[0m\n", color_p, paths_klee, paths_forest,
		 																color_t, time_klee, time_forest,
																		color_c, coverage_forest, coverage_klee);

	end_pass("compare_klee");

}

