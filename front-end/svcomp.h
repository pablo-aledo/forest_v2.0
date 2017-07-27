/*
 * =====================================================================================
 * /
 * |     Filename:  svcomp.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 05:33:27 PM
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



#ifndef _SVCOMP_H_
#define _SVCOMP_H_

#include <sstream>
#include <string>
#include <vector>
#include "cmd_options.h"
#include "heuristic.h"
#include <unistd.h>
#include <sys/wait.h>

using namespace std;

bool is_parseable();
void svcomp();
string svcomp_get_result();
float svcomp_get_time();
string check_without_instrumentation();
bool get_overflow();
bool get_doublefree();
void fill_dots(string& line, int length);
map<string, int> read_position_to_token();
vector<string> get_trace_positions();
void output_witness(vector<int> tokens);
void output_empty_witness();
void generate_witness();
bool check_witness();


#endif /* end of include guard: _SVCOMP_H_ */
