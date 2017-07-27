/*
 * =====================================================================================
 * /
 * |     Filename:  wrapper.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/14/2013 03:25:05 AM
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

#include "wrapper.h"
#include "options.h"
#include "operators.h"
#include "solver_wrapper.h"
#include "operators.h"
#include "measurement.h"
#include "timer.h"
#include "z3_solver.h"
#include "z3_bitvector.h"
#include "linear_solver.h"
#include "mixed_int.h"
#include "mixed_bblast.h"
#include "polynomic_solver.h"
#include "all_solvers.h"
#include "z3_realint.h"
#include "linear_bblast.h"
#include "database.h"
#include "interpolant_solver.h"
#include "uppaal.h"
#include "concurrency_backend.h"
#include "memory_allocator.h"
#include "pre_post.h"

Options* options           = new Options();
Operators* operators       = new Operators();
SolverWrapper* solver      = new Z3RealInt();
Database* database         = new Database();
Measurement* measurement   = new Measurement();
Timer* timer               = new Timer();
Uppaal* uppaal             = new Uppaal();
Concurrency* concurrency   = new Concurrency();
MemAlloc* memory_allocator = new MemAlloc();
PrePost* pre_post          = new PrePost();

void cast_instruction(char* _dst, char* _src, char* _type, char* _sext){
	timer->start_timer();
       	operators->cast_instruction(_dst, _src, _type, _sext); 
	timer->end_timer("cast_instruction");
}

void NonAnnotatedCallInstr( char* _fn_name, char* _ret_type ){
	if(options->cmd_option_bool("checkerror")){
		operators->checkerror_fn(_fn_name);
	} else {
		timer->start_timer();
		operators->NonAnnotatedCallInstr(_fn_name, _ret_type);
		timer->end_timer("NonAnnotatedCallInstr");
	}
}

void CallInstr_post( char* _fn_name, char* _ret_type, char* _caller ){
	if(options->cmd_option_bool("get_concurrent_functions")){
		concurrency->callinstr_post(_fn_name);
	} else {
		timer->start_timer();
		operators->CallInstr_post( _fn_name, _ret_type, _caller );
		timer->end_timer("CallInstr_post");
	}
}

void CallInstr( char* _oplist, char* _ret_to, char* _call_id ){
	if(options->cmd_option_bool("get_concurrent_functions")){
		concurrency->callinstr(_oplist);
	} else {
		timer->start_timer();
		operators->CallInstr( _oplist,  _ret_to );
		if(options->cmd_option_bool("generate_uppaal_model")) uppaal->call_id(_call_id);
		timer->end_timer("CallInstr");
	}
}

void select_op(char* _dest, char* _cond, char* _sel1, char* _sel2 ){
	timer->start_timer();
	operators->select_op(_dest, _cond, _sel1, _sel2);
	timer->end_timer("select_op");
}

void ReturnInstr(char* _retname ){
	if(options->cmd_option_bool("checkerror")){
	} else {
	timer->start_timer();
	operators->ReturnInstr(_retname);
	if(options->cmd_option_bool("generate_uppaal_model")) uppaal->EndFn();
	timer->end_timer("ReturnInstr");
	}
}

void binary_op(char* _dst, char* _op1, char* _op2, char* _operation){
	timer->start_timer();
	operators->binary_op(_dst, _op1, _op2,_operation);
	timer->end_timer("binary_op");
}

void load_instr(char* _dst, char* _addr){
	timer->start_timer();
	operators->load_instr(_dst, _addr);
	timer->end_timer("load_instr");

}

void store_instr(char* _src, char* _addr){
	timer->start_timer();
	operators->store_instr(_src, _addr);
	timer->end_timer("store_instr");
}

void cmp_instr(char* _dst, char* _cmp1, char* _cmp2, char* _type){
	timer->start_timer();
	operators->cmp_instr(_dst, _cmp1, _cmp2, _type);
	timer->end_timer("cmp_instr");
}

void br_instr_incond(){
	timer->start_timer();
	operators->br_instr_incond();
	timer->end_timer("br_instr_incond");
}

void begin_bb(char* name){

	if(options->cmd_option_bool("visualize_coverage")){
		if(operators->get_actual_function() == "main")
			database->add_visualization_bb(string(name));
	}
	if(options->cmd_option_bool("measurement")){
		measurement->begin_bb(name);
	} else if (options->cmd_option_bool("checkerror") ){
		operators->checkerror_bb(name);
	} else {
		timer->start_timer();
		operators->begin_bb(name);
		timer->end_timer("begin_bb");
	}
}

void end_bb(char* name){
	if(options->cmd_option_bool("measurement")){
		measurement->end_bb(name);
	} else if (options->cmd_option_bool("checkerror") ){
	} else {
		timer->start_timer();
		operators->end_bb(name);
		timer->end_timer("end_bb");
	}
}

void global_var_init(char* _varname, char* _type, char* _values){
	timer->start_timer();
	operators->global_var_init(_varname, _type,_values);
	timer->end_timer("global_var_init");
}

void alloca_instr(char* _reg, char* _subtype){
	timer->start_timer();
	operators->alloca_instr(_reg, _subtype);
	timer->end_timer("alloca_instr");
}

void getelementptr(char* _dst, char* _pointer, char* _indexes, char* _offset_tree){
	timer->start_timer();
	operators->getelementptr(_dst, _pointer, _indexes,_offset_tree);
	timer->end_timer("getelementptr");
}

void begin_sim_measurement(char* functions, char* bbs){
	timer->start_timer();
	measurement->begin_sim_measurement(functions, bbs);
	timer->end_timer("begin_sim_measurement");
}

void begin_sim(){
	
	options->read_options();
	if(options->cmd_option_str("solver") == "bitvector")
		solver = new Z3BitVector();
	else if(options->cmd_option_str("solver") == "real_integer")
		solver = new Z3RealInt();
	else if(options->cmd_option_str("solver") == "linear")
		solver = new LinearSolver();
	else if(options->cmd_option_str("solver") == "polynomic")
		solver = new PolynomicSolver();
	else if(options->cmd_option_str("solver") == "mixed_int")
		solver = new MixedInt();
	else if(options->cmd_option_str("solver") == "mixed_bblast")
		solver = new MixedBblast();
	else if(options->cmd_option_str("solver") == "all_solvers")
		solver = new AllSolvers();
	else if(options->cmd_option_str("solver") == "linear_bblast")
		solver = new LinearBblast();
	else if(options->cmd_option_str("solver") == "interpolants")
		solver = new InterpolantSolver();
	else
		assert(0 && "Unknown solver");

	memory_allocator->initialize();
	pre_post->load_conditions();


	timer->start_timer();
	operators->begin_sim();
	timer->end_timer("begin_sim");
}

void BeginFn(char* _fn_name, char* _fn_oplist ){
	
	if(options->cmd_option_bool("checkerror")){
	} else {
		timer->start_timer();

		if(options->cmd_option_bool("measurement"))
			measurement->BeginFn(_fn_name);
		else
			operators->BeginFn(_fn_name, _fn_oplist);

		if(options->cmd_option_bool("generate_uppaal_model")){
			uppaal->BeginFn(_fn_name);
		}

		timer->end_timer("BeginFn");
	}
}

void EndFn(){
	if(options->cmd_option_bool("checkerror")){
	} else {
		measurement->EndFn();
		if(options->cmd_option_bool("generate_uppaal_model")){
			uppaal->EndFn();
		}
	}
}

void end_sim(){

	memory_allocator->end_sim();

	if(options->cmd_option_bool("generate_uppaal_model"))
		uppaal->end_sim();

	if(options->cmd_option_bool("measurement"))
		measurement->end_sim();
	else
		operators->end_sim();

	timer->print_times();
}

bool br_instr_cond(char* _cmp, char* _joints){
	//timer->start_timer();
	bool ret = operators->br_instr_cond(_cmp, _joints);
	//timer->end_timer("br_instr_cond");
	

	return ret;
}

void br_instr_cond_measurement(bool value){
	measurement->br_instr_cond_measurement(value);
}

void Free_fn( char* _oplist ){
	timer->start_timer();

	operators->Free_fn(_oplist);
	timer->end_timer("Free_fn");
}

short vector_short(char* _name){

	return measurement->vector_short(_name);
}


long vector_long(char* _name){

	return measurement->vector_long(_name);
}


int vector_int(char* _name){
	return measurement->vector_int(_name);
}

float vector_float(char* _name){
	return measurement->vector_float(_name);
}

char vector_char(char* _name){
	return measurement->vector_char(_name);
}

void pointer_ranges(){
	operators->pointer_ranges();
}

void Memcpy(char* a, char* b, char* c, char* d, char* e){
	timer->start_timer();
	operators->memcpy(a,b,c,d,e);
	timer->end_timer("Memcpy");
}

void assumption(char* _assumption_register){
	operators->assume(_assumption_register);
}

void assertion(char* _assertion_register){
	operators->assertion(_assertion_register);
}

char __VERIFIER_nondet_char(){ return 0; }
void __VERIFIER_error(){;}
int __VERIFIER_nondet_int(){return 0;}
unsigned int __VERIFIER_nondet_uint(){return 0;}
bool __VERIFIER_nondet_bool(){return 0;}
long __VERIFIER_nondet_long(){return 0;}
void* __VERIFIER_nondet_pointer(){return 0;}

void mutex_lock_2(char* name){

	uppaal->mutex_lock(name);
	
}


void mutex_unlock_2(char* name){

	uppaal->mutex_unlock(name);
	
}

void thread_create(pthread_t *id , void*(*name)(void *) ){
	printf("thread_create %x %x\n", id, name);
}

void thread_join(pthread_t* id){
	printf("thread_join\n");
}

void* fr_malloc(char* _register_size){
	memory_allocator->fr_malloc(_register_size);
}

void  fr_free  (char* _register_pointer){
	memory_allocator->fr_free(_register_pointer);
}

void* fr_alloca  (char* _register_size){
	memory_allocator->fr_alloca(_register_size);
}


#include <stdio.h>
#include <stdarg.h>
#include <sys/socket.h>
#include <arpa/inet.h>

int rv_connect() {
	static int fd = 0;

	if (fd == 0) {
		int err = 0;
		struct sockaddr_in server;
		server.sin_addr.s_addr = inet_addr("127.0.0.1");
		server.sin_family      = AF_INET;
		server.sin_port        = htons(13337);

		fd = socket(AF_INET, SOCK_STREAM, 0);
		if (fd < 0)
			return fd;

		err = connect(fd, (struct sockaddr *)&server, sizeof(server));
		if (err)
			fd = -1;
	}

	return fd;
}

void rv_emit_async(const char *event, const char *format, ...) {
	int socket = rv_connect();
	if (socket > 0) {
		int len = 0;
		char buffer[256];

		len += snprintf(buffer + len, sizeof(buffer) - len, "%s ", event);
		if (format) {
			va_list args;
			va_start(args, format);
			len += vsnprintf(buffer + len, sizeof(buffer) - len, format, args);
			va_end(args);
		}
		len += snprintf(buffer + len, sizeof(buffer) - len, "\n");

		send(socket, buffer, len, 0);
	}
}


void* fp_hook( char* _register_with_fp ){

	return operators->fp_hook(_register_with_fp);

}

