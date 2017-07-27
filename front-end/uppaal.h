/*
 * =====================================================================================
 * /
 * |     Filename:  uppaal.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/11/2014 04:43:34 PM
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

#ifndef _UPPAAL_H_
#define _UPPAAL_H_




#include "cmd_options.h"
#include "bc_handling.h"

typedef struct Location {
	string name;
	int x;
	int y;
} Location;

typedef struct UppaalRow {
	string src;
	string dst;
	string conditions;
	string semaphore;
	string lockunlock;
	string assigns;
} UppaalRow;



//For check_xml
typedef struct
{
	std::string name;
	std::string type;
	std::string action;
	std::string to_ite;
	std::string from_ite;
	
}info_dep_temp_t;
typedef struct
{
	std::vector<info_dep_temp_t> info_dependencies;
	std::string name;
	std::string number_threads_ite;
}info_thr_temp_t;




void generate_uppaal_model();
void compare_xml();


#endif /* end of include guard: _UPPAAL_H_ */
