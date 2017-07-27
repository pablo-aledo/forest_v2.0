/*
 * =====================================================================================
 * /
 * |     Filename:  memory_allocator.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/22/2015 02:41:28 PM
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

#include "memory_allocator.h"
#include "operators.h"
#include "solver_wrapper.h"
#include <stdio.h>
#include "utils.h"
#include "options.h"
#include "database.h"



extern Operators* operators;
extern SolverWrapper* solver;
extern Options* options;
extern Database* database;

MemAlloc::MemAlloc(){
	number_of_mallocs = 0;
}

MemAlloc::~MemAlloc(){
	
}

void MemAlloc::initialize(){
	printf("memalloc_initialize\n");

	int stack_size  = options->cmd_option_int("stack_size");
	int stack_start = options->cmd_option_int("stack_start");

	string types;
	string values;
	for ( unsigned int i = 0; i < stack_size; i++) {
		types += "IntegerTyID8,";
		values += "X,";
		solver->insert_forced_free_var("mem_" + itos(stack_start+i));
		solver->set_malloc_origin("mem_" + itos(stack_start+i), "mem_" + itos(stack_start+i));
	}

	operators->set_alloca_pointer(stack_start);
	operators->global_var_init((char*)"global_allocation_buffer", (char*)types.c_str(), (char*)values.c_str());
	operators->set_alloca_pointer(0);

}

int MemAlloc::get_size(){
	if(options->cmd_option_str("malloc_policy") == "constant")
		return stoi(solver->realvalue("frmalloc_registerunderscoresize"));

	return stoi(solver->realvalue("frmalloc_registerunderscoresize"));
}

void* MemAlloc::fr_malloc(char* register_size){

	number_of_mallocs++;

	printf("FR_MALLOC\n");


	operators->BeginFn((char*)"fr_malloc", (char*)"register_size");
	operators->begin_bb((char*)"entry");


	//int first_address  = stoi(solver->realvalue("global_allocationunderscorebuffer"));
	//int allocated_size = get_size();
	//int last_address  = first_address + allocated_size - 1;
	
	pair<int,int> minmax;
	if(solver->get_is_propagated_constant("frmalloc_registerunderscoresize")){
		int value = stoi(solver->realvalue("frmalloc_registerunderscoresize"));
		minmax = pair<int,int>(0, value-1);
	} else {
		minmax = solver->get_range("frmalloc_registerunderscoresize");
	}

	int first_address = stoi(solver->realvalue("global_allocationunderscorebuffer")) + minmax.first;
	int last_address  = stoi(solver->realvalue("global_allocationunderscorebuffer")) + minmax.second;

	operators->alloca_instr((char*)"register_ret", (char*)"PointerTyID");

	solver->assign_instruction((char*)"global_allocationunderscorebuffer", (char*)"frmalloc_registerunderscoreret");
	solver->set_first_address("frmalloc_registerunderscoreret", first_address);
	solver->set_last_address ("frmalloc_registerunderscoreret", last_address);
	solver->set_is_propagated_constant("frmalloc_registerunderscoreret");


	string name_mem = "mem_" + solver->realvalue("global_allocationunderscorebuffer");
	solver->set_freed(name_mem, false);

	string stack_step = options->cmd_option_str("stack_step");

	solver->binary_instruction((char*)"global_allocationunderscorebuffer", (char*)"global_allocationunderscorebuffer", (char*)"constant_PointerTyID_" + stack_step, (char*)"+");


	operators->ReturnInstr((char*)"register_ret");
	operators->end_bb((char*)"entry");


	return 0;
}


void* MemAlloc::fr_alloca(char* register_size){


	//number_of_mallocs++;

	printf("FR_ALLOCA\n");


	operators->BeginFn((char*)"fr_alloca", (char*)"register_size");
	operators->begin_bb((char*)"entry");


	//int first_address  = stoi(solver->realvalue("global_allocationunderscorebuffer"));
	//int allocated_size = get_size();
	//int last_address  = first_address + allocated_size - 1;
	
	pair<int,int> minmax;
	if(solver->get_is_propagated_constant("fralloca_registerunderscoresize")){
		int value = stoi(solver->realvalue("fralloca_registerunderscoresize"));
		minmax = pair<int,int>(0, value-1);
	} else {
		minmax = solver->get_range("fralloca_registerunderscoresize");
	}

	int first_address = stoi(solver->realvalue("global_allocationunderscorebuffer")) + minmax.first;
	int last_address  = stoi(solver->realvalue("global_allocationunderscorebuffer")) + minmax.second;

	operators->alloca_instr((char*)"register_ret", (char*)"PointerTyID");

	solver->assign_instruction((char*)"global_allocationunderscorebuffer", (char*)"fralloca_registerunderscoreret");
	solver->set_first_address("fralloca_registerunderscoreret", first_address);
	solver->set_last_address ("fralloca_registerunderscoreret", last_address);
	solver->set_is_propagated_constant("fralloca_registerunderscoreret");


	string name_mem = "mem_" + solver->realvalue("global_allocationunderscorebuffer");
	solver->set_freed(name_mem, false);

	string stack_step = options->cmd_option_str("stack_step");

	solver->binary_instruction((char*)"global_allocationunderscorebuffer", (char*)"global_allocationunderscorebuffer", (char*)"constant_PointerTyID_" + stack_step, (char*)"+");


	operators->ReturnInstr((char*)"register_ret");
	operators->end_bb((char*)"entry");


	return 0;
}

void  MemAlloc::fr_free(char* register_pointer){

	number_of_mallocs--;

	printf("FR_FREE\n");
	operators->BeginFn((char*)"fr_free", (char*)"register_pointer");
	operators->begin_bb((char*)"entry");


	printf("memalloc_frfree %s\n", solver->realvalue("frfree_registerunderscorepointer").c_str() );

	operators->end_bb((char*)"entry");

	operators->ReturnInstr((char*)"register_");


	if(solver->get_is_propagated_constant("frfree_registerunderscorepointer")){
		string name_mem = "mem_" + solver->realvalue("frfree_registerunderscorepointer");

		if(solver->get_freed(name_mem)){
			printf("Double_Free detected\n");
			database->insert_doublefree();
			database->insert_problem();
			exit(0);
		}
		solver->set_freed(name_mem, true);
	} else {

		pair<int,int> minmax;
		minmax = solver->get_range("frfree_registerunderscorepointer");
		for ( unsigned int i = minmax.first; i <= minmax.second; i++) {
			string name_mem = "mem_" + itos(i);
			if(solver->get_freed(name_mem)){
				printf("Double_Free detected\n");
				solver->add_bt("frfree_registerunderscorepointer", itos(i-1));
				solver->add_lt("frfree_registerunderscorepointer", itos(i+1));
				solver->solve_problem();
				database->insert_doublefree();
				database->insert_problem();
				exit(0);
			}
			solver->set_freed(name_mem, true);
		}


	}


	
}

void  MemAlloc::end_sim(){
	if(number_of_mallocs > 0){
		printf("Memory leak\n");
		solver->solve_problem();
		database->insert_memoryleak();
		database->insert_problem();
		exit(0);
	}
}


