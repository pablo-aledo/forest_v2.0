/*
 * =====================================================================================
 * /
 * |     Filename:  pass_handler.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:08:03 PM
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


#ifndef _PASS_HANDLER_H_
#define _PASS_HANDLER_H_

#include <string>
#include "bc_handling.h"
#include "database_frontend.h"
#include "coverage.h"
#include "klee.h"
#include "heuristic.h"
#include "goanna_fpr.h"
#include "svcomp.h"
#include "concurrent.h"

using namespace std;



void do_pass(string passname);
bool done(string passname);
void start_pass(string pass);
void end_pass(string passname);
void needs(string second, string first);
void disables(string second, string first);
void disable_options();


#endif /* end of include guard: _PASS_HANDLER_H_ */
