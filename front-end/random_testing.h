/*
 * =====================================================================================
 * /
 * |     Filename:  random_testing.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 06:04:36 PM
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

#ifndef _RANDOM_TESTING_H_
#define _RANDOM_TESTING_H_

#include <string>
#include <map>
#include "bc_handling.h"

using namespace std;

void random_testing();
int custom_random(string name, map<string, string> distributions);
void gen_file_vectors_random();
void gen_file_free_variables_from_xml();


#endif /* end of include guard: _RANDOM_TESTING_H_ */
