/*
 * =====================================================================================
 * /
 * |     Filename:  concurrency_backend.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/27/2015 03:06:41 PM
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

#include "concurrency_backend.h"

extern SolverWrapper* solver;
extern Operators* operators;

Concurrency::Concurrency(){
	actual_id = 0;
}

Concurrency::~Concurrency(){
	
}

void Concurrency::callinstr_post(char* _fn_name){

	printf("callinstr_post %s\n", _fn_name);
	string fn_name = string(_fn_name);

	if(fn_name == "thread_create"){
		static int n = 0;
		if(n++ == 10){
			end_sim();
			exit(0);
		}
		//printf("concurrency %s %s\n", _fn_name, oplist.c_str() );
		string register_id       = tokenize(oplist, ",")[0];
		string register_function = tokenize(oplist, ",")[1];

		string content_id       = solver->realvalue(operators->name(register_id));
		string content_function = solver->realvalue(operators->name(register_function));
		string mem_name         = "mem_" + content_id;

		//printf("concurrency %s %s\n", content_id.c_str(), content_function.c_str() );


		string function = solver->realvalue(operators->name(register_function));

		string constant_id = "constant_IntegerTyID32_" + itos(actual_id);
		solver->assign_instruction(constant_id, mem_name);
		//printf("function: %s\n", function.c_str());
		
		map_functions[actual_id] = content_function;


		current_functions.insert(function);

		printf("starting_function %s\n", content_function.c_str());

		actual_id++;


	}

	if(fn_name == "thread_join"){
		printf("concurrency %s %s\n", _fn_name, oplist.c_str() );

		string register_id       = tokenize(oplist, ",")[0];
		string content_id       = solver->realvalue(operators->name(register_id));

		string content_function = map_functions[stoi(content_id)];

		printf("stopping function %s\n", content_function.c_str());

		concurrent_functions.insert(current_functions);

		current_functions.erase(current_functions.find(content_function));

	}

}

void Concurrency::end_sim(){
	printf("concurrency::end_sim\n");
	FILE* file = fopen(tmp_file("concurrent_functions").c_str(), "a");
	for( set<set<string> >::iterator it = concurrent_functions.begin(); it != concurrent_functions.end(); it++ ){
		set<string> functions = *it;
		for( set<string>::iterator it2 = functions.begin(); it2 != functions.end(); it2++ ){
			fprintf(file, "%s,", it2->c_str());
		}
		fprintf(file, "\n");
	}

	for( set<string>::iterator it = current_functions.begin(); it != current_functions.end(); it++ ){
		fprintf(file, "%s,", it->c_str());
	}
	fprintf(file, "\n");

	fclose(file);
	
}

void Concurrency::callinstr(char* _oplist){

	oplist = string(_oplist);

}
