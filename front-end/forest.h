/*
 * =====================================================================================
 * /
 * |     Filename:  forest.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/16/2013 04:00:43 AM
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


#ifndef _FOREST_H_
#define _FOREST_H_

#include "./tinyxml.h"
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <fstream>
#include <iostream>
#include "cmd_options.h"
#include "database_frontend.h"
#include "pass_handler.h"
#include "bc_handling.h"
#include "svcomp.h"
#include "concurrent.h"
#include "random_testing.h"
#include "models.h"
#include "uppaal.h"
#include "goanna_fpr.h"

using namespace std;

void make_bc();
void run();
void test();
void clean();
void final();
void measure_coverage();
void check_coverage();
void options_to_file();
void set_option( string key, string value );
void do_klee();
void minimal_test_vectors_to_db();
void db_command(string command);
void get_result();
void vim();
void valgrind();
void clean_tables();
void klee_coverage();
void tests_from_klee();
string cmd_option_str(string option);
bool cmd_option_bool(string option);
void get_static_heuristic();



#endif /* end of include guard: _FOREST_H_ */
