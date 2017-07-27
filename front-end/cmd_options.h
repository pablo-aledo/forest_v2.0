/*
 * =====================================================================================
 * /
 * |     Filename:  cmd_options.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:07:43 PM
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


#ifndef _CMD_OPTIONS_H_
#define _CMD_OPTIONS_H_



#include <vector>
#include "./tinyxml.h"
#include <string>
#include <map>
#include "utils_frontend.h"
#include "pass_handler.h"
#include <fstream>
#include <iostream>

using namespace std;


void set_option( string key, string value );
void load_cmd_options(int argc, const char** argv );
int cmd_option_int(string option);
string cmd_option_str(string option);
bool cmd_option_bool(string option);
float cmd_option_float(string option);
vector<string> cmd_option_string_vector(string option);
vector<int> cmd_option_int_vector(string option);
vector<float> cmd_option_float_vector(string option);
void load_file_options(string file);
void load_default_options();
void load_file_options();
void cmd_option_set(string key, string value );
void options_to_file();
void set_current_path();
void set_project_path( string file );
string get_project_path();
string get_current_path();
void expand_options();

#endif /* end of include guard: _CMD_OPTIONS_H_ */
