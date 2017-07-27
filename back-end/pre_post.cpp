/*
 * =====================================================================================
 * /
 * |     Filename:  pre_post.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/02/2015 06:11:41 PM
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

#include "pre_post.h"


extern SolverWrapper* solver;
extern Database* database;
extern Options* options;
extern Operators* operators;


PrePost::PrePost(){
	
}

PrePost::~PrePost(){
	
}

void PrePost::load_conditions(){

	vector<string> pre_post_files = options->cmd_option_vector_str("pre_post_file");

	for( vector<string>::iterator it = pre_post_files.begin(); it != pre_post_files.end(); it++ ){

		ifstream input(it->c_str());
		string line;
		string function;

		while( getline( input, line ) ) {

			if(line[0] == '#') continue;

			if(line.substr(0,8) == "function"){
				function = line.substr(9);
			}

			if(line.substr(0,24) == "content:(= preconditions"){
				int p1 = 25;
				int p2 = line.length() - 1;
				string precondition = line.substr(p1, p2-p1);
				preconditions[function].insert(precondition);
			}

			if(line.substr(0,25) == "content:(= postconditions"){
				int p1 = 26;
				int p2 = line.length() - 1;
				string postcondition = line.substr(p1, p2-p1);
				postconditions[function].insert(postcondition);
			}

			if(line.substr(0,5) == "input"){
				int p1 = 6;
				string variable = line.substr(p1);
				variables[function].insert(variable);
			}

		}
	}

}

set<string> PrePost::get_preconditions(string function){

	return preconditions[function];

}

set<string> PrePost::get_postconditions(string function){

	return postconditions[function];

}



void PrePost::check_preconditions( set<string> preconditions ){
	for( set<string>::iterator it = preconditions.begin(); it != preconditions.end(); it++ ){
		printf("precondition %s\n", it->c_str());
	}



	if(int pid = fork()){
		int status; waitpid(pid, &status, 0);
	} else {

		string condition = "(or ";
		for( set<string>::iterator it = preconditions.begin(); it != preconditions.end(); it++ ){
			condition += "(not " + *it + ")";
		}
		condition += ")";

		string function = operators->get_actual_function();

		set<string> vars = variables[function];

		for( set<string>::iterator it = vars.begin(); it != vars.end(); it++ ){
			string hint = *it;
			string var = solver->find_by_name_hint(hint);

			if(solver->content_smt(var) == ""){
				solver->insert_variable(var, hint);
				//myReplace(condition, hint, "." + hint + ".");
			} else {
				myReplace(condition, hint, solver->content_smt(var));
			}
		}

		myReplace(condition, "constant_IntegerTyID32_5", "5");
		myReplace(condition, "constant_IntegerTyID32_1", "1");
		
		solver->add_smt(condition);
		solver->solve_problem();
		if(solver->solvable_problem()){
			database->insert_precondition_violation();
			printf("Precondition violated\n");
		}
		exit(0);
	}
	
	//exit(0);
	
}


void PrePost::add_postconditions( set<string> postconditions ){

	string condition = "(and ";
	string function = operators->get_actual_function();
	set<string> vars = variables[function];

	for( set<string>::iterator it = postconditions.begin(); it != postconditions.end(); it++ ){
		printf("postcondition %s\n", it->c_str());

		condition += *it + " ";
	}

	for( set<string>::iterator it = vars.begin(); it != vars.end(); it++ ){
		string hint = *it;
		string var = solver->find_by_name_hint(hint);

		if(solver->content_smt(var) == ""){
			solver->insert_variable(var, hint);
			//myReplace(condition, hint, "-" + hint + "." + var + "-");
		} else {
			myReplace(condition, hint, solver->content_smt(var));
		}

	}

	condition += ")";
	
	solver->add_smt(condition);

}
