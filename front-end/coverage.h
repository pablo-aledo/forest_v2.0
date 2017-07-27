/*
 * =====================================================================================
 * /
 * |     Filename:  coverage.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:25:01 PM
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

#ifndef _COVERAGE_H_
#define _COVERAGE_H_

#include "pass_handler.h"
#include "database_frontend.h"

void measure_coverage();
void check_coverage();
void gen_final_for_measurement();


#endif /* end of include guard: _COVERAGE_H_ */
