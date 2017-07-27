/*
 * =====================================================================================
 * /
 * |     Filename:  utils_frontend.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:13:18 PM
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

#ifndef _UTILS_FRONTEND_H_
#define _UTILS_FRONTEND_H_

#include <vector>
#include <string>
#include <set>
#include <stdlib.h>
#include <stdio.h>
#include <sstream>
#include "cmd_options.h"

using namespace std;

int stoi(string str);
vector<string> tokenize(const string& str,const string& delimiters) ;
void systm( string cmd );
string tmp_file(string file);
string prj_file(string file);
string tmp_dir();
void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) ;
bool is_bc(string file);
bool is_bs(string file);
set<string> vtos(vector<string> vect);
void printvector( vector<string> v );
string itos(int i);
set<string> setintersection(set<string> set_a, set<string> set_b);
float stof(string str);


#endif /* end of include guard: _UTILS_FRONTEND_H_ */
