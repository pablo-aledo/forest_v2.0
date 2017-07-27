/*
 * =====================================================================================
 * /
 * |     Filename:  klee.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:41:05 PM
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



#ifndef _KLEE_H_
#define _KLEE_H_

#include "pass_handler.h"

void do_klee();
void klee_coverage();
void make_initial_bc_klee();
void tests_from_klee();
void compare_klee();


#endif /* end of include guard: _KLEE_H_ */
