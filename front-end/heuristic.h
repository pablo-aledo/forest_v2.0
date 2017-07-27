/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:44:32 PM
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

#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "pass_handler.h"
#include "svcomp.h"




typedef struct PathAndConds {
	string path;
	string conds;
	int width;
	string last_bb;
	string file_initializations;
} PathAndConds;



void get_static_heuristic();
void drive_frontend();
void load_heuristics();

void add_paths(set<PathAndConds>& frontier);
void print_frontier(set<PathAndConds> frontier);
void print_frontier_simple(set<PathAndConds> frontier);
void print_frontier_simple_2(set<PathAndConds> frontier);
string get_last_bb();
int width(string conds);
set<string> get_heuristics();


#endif /* end of include guard: _HEURISTIC_H_ */
