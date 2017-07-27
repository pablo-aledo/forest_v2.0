/*
 * =====================================================================================
 * /
 * |     Filename:  database_frontend.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:45:06 PM
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

#ifndef _DATABASE_FRONTEND_H_
#define _DATABASE_FRONTEND_H_



#include <string>
#include "cmd_options.h"




using namespace std;



typedef struct FreeVariableInfo{
	string name;
	string type;
	string position;

} FreeVariableInfo;




void db_command(string command);
void db_command_visible(string command);
void show_results();
void show_coverage();
void clean_tables();
void minimal_test_vectors_to_db();
void create_table_minimal_test_vectors();
vector< map<string, string> > vector_of_test_vectors();
string get_position(string name);
vector<FreeVariableInfo> get_free_variables();
void gen_file_free_variables();
set<vector<string> > minimal_vectors();
set<vector<string> > pivot( map< int, map<string, string> > values, set<string> names );
bool dontcares( vector<string> v );
bool covers_bool( vector<string> v1, vector<string> v2 );
vector<string> covers( vector<string> v1, vector<string> v2 );
void gen_file_vectors();
void show_test_vectors();
char get_argv_char(int testvector, int i);
void show_argvs();


#endif /* end of include guard: _DATABASE_FRONTEND_H_ */
