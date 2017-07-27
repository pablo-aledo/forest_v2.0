/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:44:18 PM
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

#include "heuristic.h"

set<string> heuristics;



inline bool operator<(const PathAndConds& lhs, const PathAndConds& rhs) {
	if(lhs.width != rhs.width) return lhs.width > rhs.width;
	return lhs.path < rhs.path;
}


void get_static_heuristic(){

	start_pass("heuristic");

	make_initial_bc();

	if(!is_parseable()){
		end_pass("heuristic");
		return;
	}

	stringstream cmd;
	string llvm_path   = cmd_option_str("llvm_path");

	// Clean optimization pass
	cmd.str("");
	//cmd << "opt -simplifycfg -instcombine -strip-dead-prototypes < file.bc > file-2.bc";
	cmd << "opt -strip-dead-prototypes < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_rmmalloc -instr_rmpthread -instr_rmputs -instr_rmassume -instr_rmmemcpy -instr_rmerror -instr_rmindet -instr_addassert < file-3.bc > file-4.bc";
	systm(cmd.str().c_str());

	options_to_file();

	// Heuristic optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestHeuristic.so -pathfinder < file-4.bc > file-5.bc";
	systm(cmd.str().c_str());

	end_pass("heuristic");

}

void drive_frontend(){

	//printf("drive_frontend\n");

	set_option("follow_path", "true");
	set_option("single_step", "true");

	set<PathAndConds> frontier;

	load_heuristics();

	int n = 0;
	do {
		PathAndConds first;
		if(frontier.size()){

			bool pick_random = cmd_option_bool("random_branching");
			//bool pick_random = true;
			if(pick_random){
				int pick = rand() % frontier.size() - 1;
				set<PathAndConds>::iterator it = frontier.begin(); it++;
				while(pick > 0){
					it++; pick--;
				}
				first = *(it);
				frontier.erase(it);
			} else {
				first = *(frontier.begin());
				frontier.erase(frontier.begin());
			}
		}

		set_option("path", first.path);
		set_option("file_initializations", first.file_initializations);

		options_to_file();

		db_command("delete from frontend;");
		db_command("delete from results;");
		db_command("delete from last_bb;");
		db_command("delete from variables;");

		// Run resulting file
		stringstream cmd;
		cmd << "./" << cmd_option_str("output_file");
		systm(cmd.str().c_str());

		add_paths(frontier);

		if(n++ == cmd_option_int("max_depth"))
			exit(0);

		if(cmd_option_bool("show_frontier")){
			printf("last_bb %s\n", get_last_bb().c_str() ); // last one executed.
			// frontier contains the constraints to get to last_bb + the last constraint
			
			if(get_last_bb() == cmd_option_str("target_node")){
				printf("Node hitted\n");
				//exit(0);
				break;
			}

			print_frontier(frontier);

			if(cmd_option_bool("stop_in_frontier"))
				getchar();
		}


	} while(frontier.size());

}

void load_heuristics(){

	ifstream input(tmp_file("heuristics").c_str());
	string line;
	
	while( getline( input, line ) ) {
		if(line != "")
		heuristics.insert(line);
	}
	
}

void add_paths(set<PathAndConds>& frontier){

	stringstream action;

	action << "echo 'select path from frontend;' | sqlite3 database.db > paths";
	systm(action.str());

	action.str("");
	action << "echo 'select conditions from frontend;' | sqlite3 database.db > conditions";
	systm(action.str());


	action.str("");
	action << "echo 'select file_initializations from frontend;' | sqlite3 database.db > file_initializations";
	systm(action.str());

	string line;

	vector<string> paths;
	vector<string> conds;
	vector<string> file_initializations;

	{
		ifstream input(tmp_file("paths").c_str());
		while( getline( input, line ) ) {
			paths.push_back(line);
		}
	}
	
	{
		ifstream input(tmp_file("conditions").c_str());
		while( getline( input, line ) ) {
			conds.push_back(line);
		}
	}

	{
		ifstream input(tmp_file("file_initializations").c_str());
		while( getline( input, line ) ) {
			file_initializations.push_back(line);
		}
	}


	assert(paths.size() == conds.size());

	for ( unsigned int i = 0; i < paths.size(); i++) {
		PathAndConds path_and_cond = {paths[i], conds[i], width(conds[i]), get_last_bb(), file_initializations[i]};
		frontier.insert(path_and_cond);
	}




}

void print_frontier(set<PathAndConds> frontier){


	int maxlength = 0;
	for( set<PathAndConds>::iterator it = frontier.begin(); it != frontier.end(); it++ ){
		string path = it->path;
		if(path.length() > maxlength)
			maxlength = path.length();
	}

	//printf("%d %d\n", frontier.size(), maxlength);

	printf("frontier:(\e[33m %lu %d \e[0m) ", frontier.size(), maxlength);
	for( set<PathAndConds>::iterator it = frontier.begin(); it != frontier.end(); it++ ){
		string path = it->path;
		string path2;
		for ( unsigned int i = 0; i < path.length(); i++) {
			path2 += (path[i]=='T')?"\e[32mT\e[0m":"\e[31mF\e[0m";
		}

		printf("%s:(%s%d,%s,%s), ", path2.c_str(), it->conds.c_str(), it->width, it->last_bb.c_str(), it->file_initializations.c_str());
	}
	printf("\n");

	//getchar();
}

void print_frontier_simple(set<PathAndConds> frontier){

	//printf("frontier:(%lu) ", frontier.size());
	//for( set<PathAndConds>::iterator it = frontier.begin(); it != frontier.end(); it++ ){
	set<PathAndConds>::iterator it = frontier.begin();{
		string path = it->path;
		string path2;
		for ( unsigned int i = 0; i < path.length(); i++) {
			path2 += (path[i]=='T')?"\e[32mT\e[0m":"\e[31mF\e[0m";
		}

		printf("%s", path2.c_str());
	}
	printf("\n");

	//getchar();
}

void print_frontier_simple_2(set<PathAndConds> frontier){

	int maxlength = 0;
	for( set<PathAndConds>::iterator it = frontier.begin(); it != frontier.end(); it++ ){
		string path = it->path;
		if(path.length() > maxlength)
			maxlength = path.length();
	}

	printf("%d %d\n", frontier.size(), maxlength);
}

string get_last_bb(){
	stringstream command;
	command << "echo 'select last_bb from last_bb;' | sqlite3 database.db > " << tmp_file("last_bb");
	systm(command.str().c_str());
	

	ifstream input(tmp_file("last_bb").c_str());
	string line;
	
	input >> line;

	return line;


	
}

int width(string conds){
	vector<string> tokens = tokenize(conds, ",");
	set<string> tokens_set = vtos(tokens);

	return setintersection( tokens_set,heuristics).size();
}

set<string> get_heuristics(){
	return heuristics;
}
