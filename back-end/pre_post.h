/*
 * =====================================================================================
 * /
 * |     Filename:  pre_post.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/02/2015 06:11:23 PM
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

#include <set>
#include <string>
#include <map>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <sys/wait.h>
#include "solver_wrapper.h"
#include "database.h"

using namespace std;

class PrePost {
public:
	PrePost ();
	virtual ~PrePost ();
	set<string> get_preconditions(string function);
	set<string> get_postconditions(string function);

	void check_preconditions( set<string> preconditions );
	void add_postconditions( set<string> postconditions );

	void load_conditions();
private:

	map<string, set<string> > preconditions;
	map<string, set<string> > postconditions;
	map<string, set<string> > variables;
	
};
