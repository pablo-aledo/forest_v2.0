/*
 * =====================================================================================
 * /
 * |     Filename:  database.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/13/2013 09:40:22 AM
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

#include "database.h"
#include "operators.h"
#include "solver_wrapper.h"
#include "utils.h"
#include "timer.h"
#include "z3_solver.h"
#include "options.h"

#define debug true

extern SolverWrapper* solver;
extern Options* options;
extern Operators* operators;
extern Timer* timer;

vector< pair<string, string> > retsqlite;

Database::Database(){ }

Database::~Database(){;}

static int callback(void *NotUsed, int argc, char **argv, char **azColName){



	for(int i=0; i<argc; i++){
		string name = string(azColName[i] );
		string value = string(argv[i]);
		retsqlite.push_back( pair<string, string>(name, value) );
	}

	return 0;
}

void Database::check_database(){

	stringstream action;
	//action << ".tables";
	action << "select count() from problems;";
	sqlite3_exec(db, action.str().c_str(), callback, 0, NULL);
	//assert(retsqlite.size() && "Empty tables");
}

void Database::start_database(){
	debug && printf("\e[31m start_database \e[0m\n"); fflush(stdout);
	sqlite3_open("database.db", &db);
	debug && printf("\e[31m database_opened \e[0m\n"); fflush(stdout);

	check_database();

}

void Database::end_database(){
	debug && printf("\e[31m end_database \e[0m\n"); fflush(stdout);
	sqlite3_close(db);
}

void Database::insert_model_entry(string name, string content, string path_condition){

	stringstream action;
	action << "insert into models (variable,content,path) values ('" << name << "','" << content << "','" << path_condition << "');";
	printf("action %s\n", action.str().c_str() );
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
}


int Database::num_of_variables() {
	return solver->get_free_variables().size();
}

int Database::get_problem_num(){
	stringstream action;
	action << "select count() from problems;";
	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
	if(!retsqlite.size()) printf("error\n");
	assert(retsqlite.size() && "No database answer");
	int ret = stoi(retsqlite[0].second);
	return ret;
}

void Database::insert_problem(){

	stringstream action;
	string id = "(select count() from problems)";

	string path;
	vector<bool> path_stack = solver->get_path_stack();
	for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		path += (*it)?"T":"F";
	}
	
	action << "insert into problems (sat, path) values (" << (solver->solvable_problem()?1:0) << ",'" << path << "');";

	set<NameAndPosition> free_variables = solver->get_free_variables();
	for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
		string name = it->name;
		string type = solver->gettype(name);
		string position = it->position;
		action << "insert into variables values ('" << name << "','" << type << "','" << position << "'," << id << ");";
	}

	action << "insert into times values (" << id << ",'" << solver->get_solve_time() << "');";
	
	if( solver->solvable_problem() ){


		for( set<NameAndPosition>::iterator it = free_variables.begin(); it != free_variables.end(); it++ ){
			string name = it->name;
			string hint = it->position;
			//string value = (solver->realvalue(name) == "")?string("0"):solver->realvalue(name);
			string value;// = (it->value=="")?string("0"):it->value;
			if(hint.find("return_of_") != string::npos){
				value = (it->value == "")?string("0"):it->value;
			} else {
				value = (solver->realvalue(name) == "")?string("0"):solver->realvalue(name);
			}
			//string value = variables[name].real_value;
			//string hint = solver->get_name_hint(name);

			if(solver->get_first_content_value(name) != "")
				value = solver->get_first_content_value(name);

			action << "insert into results values ('" << name << "','" << value << "','" << hint << "'," << 1 << "," << id << ");";
			//debug && printf("\e[31m insert_result \e[0m name %s value %s\n", name.c_str(), value.c_str());
			printf("\e[31m insert_result \e[0m name %s value %s hint %s\n", name.c_str(), value.c_str(), hint.c_str());

		}

		map<string, Variable> variables = solver->get_map_variables();

		for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){

			if( it->second.isempty ) continue;

			string name = it->first;
			string value = solver->realvalue_mangled(name);
			string hint = variables[name].name_hint;


		}

		
	}

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}



void Database::insert_outofbounds(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'outofbounds');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


void Database::insert_divzero(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'division_by_zero');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::insert_precondition_violation(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'precondition_violation');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::insert_assertion(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'assertion');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::insert_remzero(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'remainder_by_zero');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


void Database::insert_doublefree(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'double_free');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


void Database::insert_memoryleak(){

	insert_problem();

	string id = "(select count() from problems)";

	stringstream action;
	action << "insert into exceptions values (" << id << ",'memory_leak');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


void Database::drop_concurrency_tables(){

	debug && printf("\e[31m drop concurrency_table \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "drop table concurrency;";
	action << "drop table loads;";
	action << "drop table stores;";
	action << "drop table sync;";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::create_concurrency_tables(){

	debug && printf("\e[31m create table concurrency \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "create table concurrency(";
	action << "lockunlock varchar(50),";
	action << "mutex_name varchar(50),";
	action << "sync_name  varchar(50),";
	action << "conds      varchar(50)";
	action << ");";
	action << "create table loads(";
	action << "pos varchar(50)";
	action << ");";
	action << "create table stores(";
	action << "pos varchar(50),";
	action << "value varchar(50),";
	action << "sync_point varchar(50)";
	action << ");";
	action << "create table sync(";
	action << "pos varchar(50),";
	action << "stack varchar(50)";
	action << ");";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


}

void Database::database_insert_concurrency(string lockunlock, string mutex_name, string sync_name, string conds){

	if( exists_in_concurrency(lockunlock, mutex_name, sync_name, conds) ) return;

	debug && printf("\e[31m insert into concurrency \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "insert into concurrency values (\"" << lockunlock << "\",\"" << mutex_name << "\",\"" << sync_name << "\",\"" << conds << "\");";
	//printf("%s\n", action.str().c_str());
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
}

void Database::insert_load(string pos){

	debug && printf("\e[31m insert load\e[0m\n"); fflush(stdout);

	stringstream action;
	action << "insert into loads values ('" << pos << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
	
}

void Database::insert_store(string pos, string content, string sync_name){

	if(exists_in_stores(pos, content, sync_name)) return;

	debug && printf("\e[31m insert store\e[0m\n"); fflush(stdout);




	stringstream action;
	action << "insert into stores values ('" << pos << "','" << content << "','" << sync_name << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

bool Database::exists_in_stores(string pos, string content, string sync_name){

	stringstream action;
	action << "select * from stores where ";
	action << "pos        = \"" << pos << "\" and ";
	action << "value      = \"" << content << "\" and ";
	action << "sync_point = \"" << sync_name << "\";";


	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	printf("accion %s %lu\n", action.str().c_str(), retsqlite.size());

	return retsqlite.size() > 0;


}

bool Database::exists_in_sync(string syncname, set<string> sync_points){

	stringstream stackstr;
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		stackstr << *it << ",";
	}
	

	stringstream action;
	action << "select * from sync where ";
	action << "pos = \"" << syncname << "\" and ";
	action << "stack = \"" << stackstr.str() << "\";";


	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("accion %s %lu\n", action.str().c_str(), retsqlite.size());

	return retsqlite.size() > 0;


}

void Database::insert_sync_points(string sync_name, set<string> sync_points){

	if(exists_in_sync(sync_name, sync_points)) return;

	printf("\e[31m insert sync\e[0m\n"); fflush(stdout);

	stringstream action;
	action << "insert into sync values ('" << sync_name << "','";
	for( set<string>::iterator it = sync_points.begin(); it != sync_points.end(); it++ ){
		action << *it << ",";
	}
	action << "');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


}

set<string> Database::list_semaphores(){

	debug && printf("\e[31m list_semaphores \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select mutex_name from concurrency;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}
	//ret.insert("a"); ret.insert("b"); ret.insert("c");

	return ret;
}

void Database::load_concurrency_table(map<string, set<string> >& ret){

	//ret["a"].insert("d");
	//ret["b"].insert("e"); ret["b"].insert("f");
	//ret["c"].insert("x");
	//debug && printf("\e[31m load_concurrency_table \e[0m\n"); fflush(stdout);

	set<string> all_semaphores = list_semaphores();

	for( set<string>::iterator it = all_semaphores.begin(); it != all_semaphores.end(); it++ ){
		stringstream action;
		action << "select sync_name from concurrency where mutex_name=\"" << (*it) << "\" and lockunlock=\"unlock\";";

		retsqlite.clear();
		sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

		if(!retsqlite.size()){
			printf("mutex %s\n", it->c_str());
			assert( 0 && "no unlocking of semaphore");
		}

		for( vector<pair<string, string> >::iterator it2 = retsqlite.begin(); it2 != retsqlite.end(); it2++ ){
			ret[(*it)].insert(it2->second);
		}
	}


	
	//for( map<string,set<string> >::iterator it = ret.begin(); it != ret.end(); it++ ){
		//printf("%s: ", it->first.c_str());
		//set<string> sec = it->second;
		//for( set<string>::iterator it2 = sec.begin(); it2 != sec.end(); it2++ ){
			//printf("%s ", it2->c_str());
		//}
		//printf("\n");
	//}
	

}

set<string> Database::list_unlock_points(){

	//debug && printf("\e[31m list_unlock_points \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select pos from sync;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}
	//ret.insert("a"); ret.insert("b"); ret.insert("c");
	//
	
	//printf("list_unlock_points.size %lu\n", ret.size()); fflush(stdout);

	return ret;

}

string Database::lockunlock(string sync_point){
	debug && printf("\e[31m lockunlock %s \e[0m\n", sync_point.c_str()); fflush(stdout);


	stringstream action;
	action << "select lockunlock from concurrency where sync_name=\"" << sync_point << "\";";


	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}

	string ret2 = *(ret.begin());

	//printf("action %s %s\n", action.str().c_str(), ret2.c_str() );
	
	return ret2;

}

string Database::semaphore_of(string sync_point){

	debug && printf("\e[31m semaphore of \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select mutex_name from concurrency where sync_name=\"" << sync_point << "\";";

	//printf("action %s\n", action.str().c_str());

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}
	
	//printf("semaphore_of.size %lu\n", ret.size()); fflush(stdout);

	return *(ret.begin());
}

set<string> Database::list_lock_points(){

	//debug && printf("\e[31m list_lock_points \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select sync_name from concurrency where lockunlock=\"lock\";";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}
	//ret.insert("a"); ret.insert("b"); ret.insert("c");
	//
	
	//printf("list_lock_points.size %lu\n", ret.size()); fflush(stdout);

	return ret;

}

set<vector<string> > Database::get_paths_to(string dest){


	//debug && printf("\e[31m get_paths_to \e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select stack from sync where pos=\"" << dest << "\";";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	set<vector<string> > ret;

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		string tokens = it->second;
		vector<string> path = tokenize(tokens, ",");
		//vector<string> tokens = tokenize(*it, ",");
		//for( vector<string>::iterator it2 = tokens.begin(); it2 != tokens.end(); it2++ ){
			//if(*it2 != dest)
				//path.push_back(*it2);
		//}
		ret.insert(path);
	}
	//ret.insert("a"); ret.insert("b"); ret.insert("c");

	return ret;

}

void Database::load_stores(map<string, set<pair<string, string> > >& stores){

	//debug && printf("\e[31m load_stores\e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select pos,value,sync_point from stores;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("load_stores_num %lu\n", retsqlite.size());

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); ){
		
		string pos = it->second;          it++;
		string value = it->second;        it++;
		string sync_point = it->second;   it++;
		
		pair<string, string> pos_and_value(pos, value);

		stores[sync_point].insert(pos_and_value);


		//printf("storesss %s\n", tokens.c_str());
		//vector<string> path = tokenize(tokens, ",");
		//vector<string> tokens = tokenize(*it, ",");
		//for( vector<string>::iterator it2 = tokens.begin(); it2 != tokens.end(); it2++ ){
			//if(*it2 != dest)
				//path.push_back(*it2);
		//}
		//ret.insert(path);
	}
	//ret.insert("a"); ret.insert("b"); ret.insert("c");

}

set<string> Database::list_sync_points(){


	set<string> ret;

	//debug && printf("\e[31m list_sync_points\e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select sync_name from concurrency;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("list_sync_points.size %lu\n", retsqlite.size());

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++){
		
		string sync_name = it->second;

		ret.insert(sync_name);


	}

	return ret;
}

void Database::load_stacks(map<string, string>& stacks){

	//debug && printf("\e[31m load_stacks\e[0m\n"); fflush(stdout);

	stringstream action;
	action << "select sync_name,conds from concurrency;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("load_stacks_num %lu\n", retsqlite.size());

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); ){
		
		string sync_name = it->second;          it++;
		string conds     = it->second;        it++;

		if(conds == "") conds = " true ";
		
		stacks[sync_name] = conds;


	}
}

set<string> Database::list_store_sync_points(){
	


	//debug && printf("\e[31m load_stacks\e[0m\n"); fflush(stdout);

	set<string> ret;

	stringstream action;
	action << "select sync_name from concurrency;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("list_store_sync_points %lu\n", retsqlite.size());

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); ){
		
		string sync_name = it->second;          it++;

		ret.insert(sync_name);

	}


	return ret;

}

void Database::insert_global_type(string name, string type, string position){

	if( exists_in_global_types(name) ) return;

	debug && printf("\e[31m insert global type %s %s\e[0m\n", name.c_str(), type.c_str()); fflush(stdout);

	stringstream action;
	action << "insert into global_types values (\"" << name << "\",\"" << type << "\",\"" << position << "\");";
	//printf("%s\n", action.str().c_str());
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

bool Database::exists_in_global_types(string name){

	stringstream action;
	action << "select * from global_types where ";
	action << "pos = \"" << name << "\";";


	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	return retsqlite.size() > 0;
}

set<pair<string, string> > Database::get_sync_global_types(){

	set<pair<string, string> > ret;

	stringstream action;
	action << "select pos,type from global_types;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); ){
		
		string pos = it->second;          it++;
		string type = it->second;          it++;

		pair<string, string> pos_and_type = pair<string, string>(pos, type);
		ret.insert(pos_and_type);

	}


	return ret;
}

bool Database::exists_in_concurrency(string lockunlock, string mutex_name, string sync_name, string conds){

	stringstream action;
	action << "select * from concurrency where ";
	action << "lockunlock = \"" << lockunlock << "\" and ";
	action << "mutex_name = \"" << mutex_name << "\" and ";
	action << "sync_name  = \"" << sync_name  << "\" and ";
	action << "conds      = \"" << conds << "\";";


	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	//printf("accion %s %lu\n", action.str().c_str(), retsqlite.size());

	return retsqlite.size() > 0;


}

void Database::start_database_measurement(){
	debug && printf("\e[31m start_database \e[0m\n"); fflush(stdout);
	sqlite3_open("database.db", &db);
}

void Database::end_database_measurement(){
	debug && printf("\e[31m end_database \e[0m\n"); fflush(stdout);
	sqlite3_close(db);
}

void Database::insert_measurement(string name, string value){

	stringstream action;

	action << "insert into measurements values ('" << name << "','" << value << "');";

	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


}

void Database::insert_problem_measurement(){

	//stringstream action;
	//string id = "(select count() from problems)";

	//string path;
	//for( vector<bool>::iterator it = path_stack.begin(); it != path_stack.end(); it++ ){
		//path += (*it)?"T":"F";
	//}
	
	//action << "insert into problems (path) values (" << "'" << path << "');";

	//printf("action %s\n", action.str().c_str() );

	//sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

inline bool operator<(const NameAndType& lhs, const NameAndType& rhs) {
  return (lhs.name + lhs.type) < (rhs.name+rhs.type);
}

set<string> Database::global_stores(string sync_name){

	set<string> ret;

	stringstream action;
	//action << "select pos from stores where sync_point=\"" << sync_name << "\";";
	action << "select pos from stores;";

	printf("global_stores action %s\n", action.str().c_str());

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end();it++ ){
		ret.insert(it->second);
	}

	printf("global_stores %s size %lu\n", sync_name.c_str(), ret.size());
	

	return ret;


}

set<string> Database::global_variables(){

	set<string> ret;

	stringstream action;
	//action << "select pos from stores where sync_point=\"" << sync_name << "\";";
	action << "select pos from global_types;";

	printf("global_variables action %s\n", action.str().c_str());

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end();it++ ){
		ret.insert(it->second);
	}

	//printf("global_variables %s size %lu\n", sync_name.c_str(), ret.size());
	

	return ret;


}

set<NameAndType> Database::get_shared_vars(){

	set<NameAndType> ret;

	stringstream action;
	action << "select pos,type from global_types;";

	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); ){
		string pos = it->second; it++;
		string type = it->second; it++;
		NameAndType elem = {pos, type};
		ret.insert(elem);
	}
	

	return ret;


}

void Database::insert_frontend_interface(){
	string path = solver->get_path_stack_str();
	//string conditions = solver->get_comma_stack_conditions();
	string conditions2 = solver->get_comma_stack_conditions_static();
	//string function_and_bb = operators->get_actual_function() + "_" + operators->get_actual_bb();
	string file_initializations = operators->get_file_initializations();


	//printf("Database::insert_frontend_interface %s %s %s\n", path.c_str(), conditions2.c_str(), file_initializations.c_str());
	
	

	//printf("function_and_bb %s\n", function_and_bb.c_str());

	stringstream action;
	action << "insert into frontend values ('" << path << "','" << conditions2 << "','" << file_initializations << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::insert_last_bb(string function_name, string bb_name){

	//string function_and_bb = operators->get_actual_function() + "_" + operators->get_actual_bb();
	string function_and_bb = function_name + "_" + bb_name;

	printf("function_and_bb %s\n", function_and_bb.c_str());

	stringstream action;

	action.str("");
	action << "delete from last_bb;";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	action.str("");
	action << "insert into last_bb values ('" << function_and_bb << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::save_times(){

	printf("save timer\n");

	map<string, float> times = timer->get_times();

	for( map<string,float>::iterator it = times.begin(); it != times.end(); it++ ){
		stringstream action;
		action.str("");
		action << "insert into timer values ('" << it->first << "','" << it->second << "');";

		printf("action %s\n", action.str().c_str());

		sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
	}
}


inline bool operator<(const Variable& lhs, const Variable& rhs) {
  return lhs.name_hint+lhs.real_value > rhs.name_hint+rhs.real_value;
}

bool Database::already_covered(){


	return false;
	map<string, Variable> variables = solver->get_map_variables();
	
	static set<map<string, Variable> > previous_variables;


	bool ret = (previous_variables.find(variables) != previous_variables.end());
	
	previous_variables.insert(variables);

	for( map<string,Variable>::iterator it = variables.begin(); it != variables.end(); it++ ){
		printf("\e[32m already_covered name \e[0m %s \e[32m value \e[0m %s\n", it->first.c_str(), it->second.real_value.c_str());
	}
	

	if(ret)
		printf("\e[31m Already covered \e[0m\n");
	else
		printf("\e[31m Not covered \e[0m\n");

	return ret;

}

bool Database::already_covered_at_bb(string name){


	return false;
	pair<string, map<string, Variable> > variables = pair<string, map<string, Variable> >(name, solver->get_map_variables());
	
	static set<pair<string, map<string, Variable> > > previous_variables;


	bool ret = (previous_variables.find(variables) != previous_variables.end());
	
	previous_variables.insert(variables);

	for( map<string,Variable>::iterator it = variables.second.begin(); it != variables.second.end(); it++ ){
		printf("\e[32m already_covered name \e[0m %s \e[32m value \e[0m %s\n", it->first.c_str(), it->second.real_value.c_str());
	}
	

	if(ret)
		printf("\e[31m Already covered \e[0m\n");
	else
		printf("\e[31m Not covered \e[0m\n");

	return ret;

}

void Database::add_interpolant(string position, string condition){

	
	stringstream action;
	action << "insert into interpolants values ('" << position << "','" << condition << "');";
	//printf("action %s\n", action.str().c_str() );
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

set<string> Database::get_interpolants(string position){

	stringstream action;
	action << "select condition from interpolants where ";
	action << "position   = \"" << position << "\";";
	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


	set<string> ret;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		ret.insert(it->second);
	}

	return ret;

}


void Database::insert_trace(){
	vector<string> functions_and_bbs = operators->get_functions_and_bbs_trace();

	string functions_and_bbs_s;
	for( vector<string>::iterator it = functions_and_bbs.begin(); it != functions_and_bbs.end(); it++ ){
		functions_and_bbs_s += (*it) + ",";
	}
	

	stringstream action;
	action << "insert into trace values ('" << functions_and_bbs_s << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
}


void uppaal_clean(string& name){

	if(options->cmd_option_bool("uppaal_simplify")){
		myReplace(name, "_Z3fn1Pv_", "");
		myReplace(name, "Z3fn1Pv_", "");
		myReplace(name, "Z3fn1Pv_registerunderscore", "");
		myReplace(name, "constant_IntegerTyID32_", "");
		myReplace(name, "register_", "");
		myReplace(name, "constant_IntegerTyID32_", "");
		myReplace(name, "constant_IntegerTyID16_", "");
		myReplace(name, "constant_PointerTyID_", "");
		myReplace(name, "registerunderscore", "");
		myReplace(name, "underscore", "");
		myReplace(name, "global_", "");
	}
}

void Database::insert_uppaal_row(string orig, string dst, string conds, string sem, string lockunlock, string assigns){

	uppaal_clean(orig);
	uppaal_clean(dst);
	uppaal_clean(conds);
	uppaal_clean(assigns);

	stringstream action;
	action << "insert into uppaal values ('" << orig << "','" << dst << "','" << conds << "',";
	action << "'" << sem << "','" << lockunlock << "','" << assigns << "');";
	printf("action %s\n", action.str().c_str());
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


void Database::insert_uppaal_variables(set<UppaalVar> variables){


	for( set<UppaalVar>::iterator it = variables.begin(); it != variables.end(); it++ ){
		stringstream action;

		string name = it->name;
		string type = it->type;
		string init = it->init;

		uppaal_clean(name);
		uppaal_clean(init);

		action << "insert into uppaal_variables values ('" << name << "','" << type << "','" << init << "');";
		printf("action %s\n", action.str().c_str());
		sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
	}
	
}

void Database::insert_variable(string name){

	stringstream action;
	string position = solver->get_name_hint(name);
	string type = solver->gettype(name);

	action << "insert into free_variables values ('" << name << "','" << position << "','" << type << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );
	
}


void Database::add_visualization_bb(string name){

	stringstream action;
	
	action.str("");
	action << "insert or ignore into visualization_bbs values ('" << name << "',0);";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

	action.str("");
	action << "update visualization_bbs set count=count+1 where name='" << name << "';";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}

void Database::insert_fi(string filename, string position, string value){
	stringstream action;
	action << "insert into file_initializations values ('" << filename << "','" << position << "','" << value << "');";
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );

}


map<string,string> Database::load_fi(string filename){

	stringstream action;
	action << "select position, value from file_initializations where ";
	action << "filename = \"" << filename << "\";";
	retsqlite.clear();
	sqlite3_exec (db, action.str().c_str(), callback,0,NULL );


	map<string, string> ret;
	string position, value;
	for( vector<pair<string, string> >::iterator it = retsqlite.begin(); it != retsqlite.end(); it++ ){
		//ret.insert(it->second);
		if(it->first == "position") position = it->second;
		if(it->first == "value") value = it->second;

		if(it->first == "value"){
			ret[position] = value;
		}

		//printf("%s %s\n", it->first.c_str(), it->second.c_str());
	}

	//exit(0);
	return ret;

}

