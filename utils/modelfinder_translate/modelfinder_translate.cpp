/*
 * =====================================================================================
 * /
 * |     Filename:  modelfinder_translate.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/01/2014 12:08:24 PM
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

#include <stdlib.h>
#include <string>
#include <sstream>
#include <iostream>
#include <fstream>
#include <vector>

using namespace std;

int main(int argc, const char *argv[])
{
	string input_file_name = string(argv[1]);

	stringstream command;

	command.str("");
	command << "cat " << string(argv[1]) << " | grep 'declare-fun' | grep state1 | awk 'BEGIN{FS=\"[: ]\"}{print $8}'";
	command << " > /tmp/variables";
	system(command.str().c_str());

	command.str("");
	command << "cat " << string(argv[1]) << " | grep 'declare-fun' | grep state1 | awk 'BEGIN{FS=\" \"}{print $4 \" \" $5 \" \" $6 \" \" $7 \" \" $8}'";
	command << " | sed 's/. *$//g'";
	command << " > /tmp/types";
	system(command.str().c_str());


	command.str(""); 
	command << "cat " << string(argv[1]) << " | grep 'preconditions' | grep 'assert' | sed -e 's/(assert //g' -e 's/.$//g'";
	command << " | sed -e 's/[^ ]*::state1::[^:]*::\\([^\\) ]*\\)/\\11/g'";
	command << " | sed -e 's/[^ ]*::state0::[^:]*::\\([^\\) ]*\\)/\\10/g'";
	command << " > /tmp/preconditions";
	system(command.str().c_str());


	command.str(""); 
	command << "cat " << string(argv[1]) << " | grep 'postconditions' | grep 'assert' | sed -e 's/(assert //g' -e 's/.$//g'";
	command << " | sed -e 's/[^ ]*::state1::[^:]*::\\([^\\) ]*\\)/\\11/g'";
	command << " | sed -e 's/[^ ]*::state0::[^:]*::\\([^\\) ]*\\)/\\10/g'";
	command << " > /tmp/postconditions";
	system(command.str().c_str());

	command.str(""); 
	command << "cat " << string(argv[1]) << " | grep 'frameconditions' | grep 'assert' | sed -e 's/(assert //g' -e 's/.$//g'";
	command << " | sed -e 's/[^ ]*::state1::[^:]*::\\([^\\) ]*\\)/\\11/g'";
	command << " | sed -e 's/[^ ]*::state0::[^:]*::\\([^\\) ]*\\)/\\10/g'";
	command << " > /tmp/frameconditions";
	system(command.str().c_str());

	vector<string> variables;
	vector<string> types;
	string preconditions;
	string postconditions;
	string frameconditions;
	string line;

	ifstream input1("/tmp/variables");
	while( getline( input1, line ) )
		variables.push_back(line);

	ifstream input2("/tmp/types");
	while( getline( input2, line ) )
		types.push_back(line);

	ifstream input3("/tmp/preconditions");
	getline( input3, preconditions);

	ifstream input4("/tmp/postconditions");
	getline( input4, postconditions);

	ifstream input5("/tmp/frameconditions");
	getline( input5, frameconditions);

	FILE* fileout = fopen(argv[2], "w");

	for ( unsigned int i = 0; i < variables.size(); i++) {
		fprintf(fileout, "input:%s0:%s\n", variables[i].c_str(), types[i].c_str());
		fprintf(fileout, "output:%s1:%s\n", variables[i].c_str(), types[i].c_str());
	}

	fprintf(fileout, "content:%s\n", preconditions.c_str());
	fprintf(fileout, "content:%s\n", postconditions.c_str());
	fprintf(fileout, "content:%s\n", frameconditions.c_str());
	
	

	return 0;
}
