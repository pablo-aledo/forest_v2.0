/*
 * =====================================================================================
 * /
 * |     Filename:  pass_handler.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:07:42 PM
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

#include "pass_handler.h"

#define debug false

std::set<string> passes_done;
std::map<string, vector<string> > needed_map;
std::map<string, set<string> > disables_map;

void do_pass(string passname){

	if(passname == "make_bc")
		make_bc();
	else if(passname == "run")
		run();
	else if(passname == "clean_tables")
		clean_tables();
	else if(passname == "vim")
		vim();
	else if(passname == "valgrind")
		valgrind();
	else if(passname == "test")
		test();
	else if(passname == "clean")
		clean();
	else if(passname == "final")
		final();
	else if(passname == "measure_coverage")
		measure_coverage();
	else if(passname == "check_coverage")
		check_coverage();
	else if(passname == "klee")
		do_klee();
	else if(passname == "get_result")
		get_result();
	else if(passname == "klee_coverage")
		klee_coverage();
	else if(passname == "heuristic")
		get_static_heuristic();
	else if(passname == "goanna_fpr")
		goanna_fpr();
	else if(passname == "svcomp")
		svcomp();
	else if(passname == "get_concurrent_functions")
		get_concurrent_functions();
	else {
		printf("Pass %s\n", passname.c_str());
		assert(0 && "Unknown pass");
	}
}

bool done(string passname){
	return passes_done.find(passname) != passes_done.end();
}

void start_pass(string pass){

	debug && printf(" ----- Starting pass %s\n", pass.c_str());


	vector<string> needed = needed_map[pass];
	for( vector<string>::iterator it = needed.begin(); it != needed.end(); it++ ){
		debug && printf("pass %s needs %s\n", pass.c_str(), it->c_str() );
		if(!done(*it)){
			debug && printf("Do it (%s)\n", it->c_str());
			do_pass(*it);
		} else {
			debug && printf("Already done (%s)\n", it->c_str());
		}
	}
}

void end_pass(string passname){
	debug && printf(" ----- Ending pass %s\n", passname.c_str());
	passes_done.insert(passname);
}

void needs(string second, string first){
	needed_map[second].push_back(first);
}

void disables(string second, string first){
	disables_map[second].insert(first);
}

void disable_options(){

	for ( unsigned int i = 0; i < 10; i++) {
		for( map<string,set<string> >::iterator it = disables_map.begin(); it != disables_map.end(); it++ ){
			string a = it->first;
			set<string> b = it->second;
			for( set<string>::iterator it2 = b.begin(); it2 != b.end(); it2++ ){
				if(cmd_option_bool(a)) set_option(*it2, "false");
			}
		}
	}
}
