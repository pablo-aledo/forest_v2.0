/*
 * =====================================================================================
 * /
 * |     Filename:  options.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:43:52 AM
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

#ifndef _OPTIONS_H_
#define _OPTIONS_H_

#include <string>
#include <map>
#include <stdio.h>
#include <string.h>
#include <fstream>
#include <iostream>
#include <stdlib.h>
#include <vector>

using namespace std;


class Options {
public:
	int cmd_option_int(string option);
	string cmd_option_str(string option);
	Options ();
	virtual ~Options ();
	void read_options();
	bool cmd_option_bool(string key);
	vector<string> cmd_option_vector_str(string key);

private:
	map<string, string> options;
	
};



#endif /* end of include guard: _OPTIONS_H_ */
