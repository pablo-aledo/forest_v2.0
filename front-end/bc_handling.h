/*
 * =====================================================================================
 * /
 * |     Filename:  bc_handling.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:14:28 PM
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


#ifndef _BC_HANDLING_H_
#define _BC_HANDLING_H_

#include "utils_frontend.h"
#include "pass_handler.h"
#include "utils_frontend.h"

void make_bc();
void compare_bc();
void compare_measure_bc();
void view_bc();
void final();
void run();
void test();
void view_dfg();
void view_dfg_2();
void vim();
void valgrind();
void clean();
void get_result();
void make_initial_bc();
void run();
void dump_forced_free_vars();
void dump_forced_free_hints();
void compare_libs();
void list_external_functions();
void linked_bc();
void create_tmp_path();
void show_timer();
void show_exceptions();
void show_interpolants();

#endif /* end of include guard: _BC_HANDLING_H_ */
