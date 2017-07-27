/*
 * =====================================================================================
 * /
 * |     Filename:  database_frontend.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:44:54 PM
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

#include "database_frontend.h"

#define SIZE_STR 1024
#define debug false


void db_command(string command){

	cmd_option_bool("verbose") && printf("\e[32m db_command %s \e[0m\n", command.c_str());

	stringstream cmd;
	cmd << "echo '" << command << "' | sqlite3 " << tmp_file("database.db");
	systm(cmd.str().c_str());

}

void db_command_visible(string command){

	cmd_option_bool("verbose") && printf("\e[32m db_command %s \e[0m\n", command.c_str());

	stringstream cmd;
	cmd << "echo '" << command << "' | sqlite3 " << tmp_file("database.db") << " > " << tmp_file("db_output");
	systm(cmd.str().c_str());

	ifstream input(tmp_file("db_output").c_str());
	string line;
	
	while( getline( input, line ) ) {
		cout << line << endl;
	}
	

}

void show_results(){


	stringstream cmd;

	// Show database results
	cmd << "echo \'.mode columns\\n.width 25 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;\'";
	cmd << " | sqlite3 " << tmp_file("database.db");



	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		printf("%s", it->c_str());
	}
	



}

void show_coverage(){


	db_command_visible( ".mode columns\\n.width 20 15\\n.headers on\\nselect * from measurements;" );

}

void clean_tables(){

	start_pass("clean_tables");

	stringstream action;

	action.str();
	action << "drop table problems;";
	action << "drop table exceptions;";
	action << "drop table variables;";
	action << "drop table results;";
	action << "drop table measurements;";
	action << "drop table frontend;";
	action << "drop table check_uppaal;";
	action << "drop table check_xml;";
	db_command( action.str() );

	action.str("");
	action << "create table problems(";
	action << "problem_id INTEGER PRIMARY KEY AUTOINCREMENT,";
	action << "sat bool,";
	action << "path varchar(50)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table exceptions(";
	action << "problem_id integer,";
	action << "exception varchar(50)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table variables(";
	action << "name varchar(50),";
	action << "type varchar(50),";
	action << "position varchar(50),";
	action << "problem_id INTEGER";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table results(";
	action << "name varchar(50),";
	action << "value varchar(50),";
	action << "name_hint varchar(50),";
	action << "is_free bool,";
	action << "problem_id INTEGER";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table measurements(";
	action << "key varchar(50),";
	action << "value varchar(50)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table statistics(";
	action << "problem_id integer,";
	action << "num_of_assertions integer,";
	action << "num_of_variables integer,";
	action << "num_of_mults integer,";
	action << "num_of_divs integer,";
	action << "num_of_sums integer,";
	action << "num_of_subs integer,";
	action << "time_ms float";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table models(";
	action << "variable varchar(50),";
	action << "content varchar(5000),";
	action << "path varchar(5000)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table frontend(";
	action << "path varchar(5000),";
	action << "conditions varchar(5000),";
	action << "file_initializations varchar(5000)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table last_bb(";
	action << "last_bb varchar(50)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table times(";
	action << "problem_id integer,";
	action << "time_ms float";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table timer(";
	action << "id varchar(50),";
	action << "time_ms float";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table interpolants(";
	action << "position varchar(50),";
	action << "condition varchar(50)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table trace (";
	action << "trace varchar(5000)";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table uppaal (";
	action << "src varchar(5000),";
	action << "dst varchar(5000),";
	action << "conditions varchar(5000),";
	action << "semaphore varchar(5000),";
	action << "lockunlock varchar(5000),";
	action << "assigns varchar(5000)";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table uppaal_variables (";
	action << "name varchar(5000),";
	action << "type varchar(5000),";
	action << "init varchar(5000)";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table free_variables(";
	action << "name varchar(5000),";
	action << "position varchar(5000),";
	action << "type varchar(5000)";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table check_uppaal (";
	action << "nameThread varchar(5000),";
	action << "nameVar varchar(5000),";
	action << "type varchar(5000),";
	action << "action varchar(5000)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table check_xml (";
	action << "nameThread varchar(5000),";
	action << "nameVar varchar(5000),";
	action << "type varchar(5000),";
	action << "action varchar(5000)";
	action << ");";
	db_command( action.str() );

	action.str("");
	action << "create table visualization_bbs(";
	action << "name varchar(5000),";
	action << "count integer,";
	action << "unique (name)";
	action << ");";
	db_command( action.str() );


	action.str("");
	action << "create table file_initializations(";
	action << "filename varchar(5000),";
	action << "position varchar(5000),";
	action << "value varchar(5000)";
	action << ");";
	db_command( action.str() );

	end_pass("clean_tables");
}

void minimal_test_vectors_to_db(){

	//if(!cmd_option_bool("test_vectors")) return;

	create_table_minimal_test_vectors();

	vector< map<string, string> > vectors = vector_of_test_vectors();

	int vect = 0;
	for( vector<map<string, string> >::iterator it = vectors.begin(); it != vectors.end(); it++,vect++ ){
		for( map<string,string>::iterator it2 = (*it).begin(); it2 != (*it).end(); it2++ ){
			//printf("%s -> %s\n", it2->first.c_str(), it2->second.c_str() );

			int vectid = vect;
			string name = it2->first;
			string value = it2->second;
			string hint = get_position(name);

			stringstream cmd;
			cmd << "insert into minimal_vectors values (" << vect << ",\"" << name << "\",\"" << hint << "\",\"" << value << "\");";
			db_command(cmd.str());

			//systm( cmd.str() );

			//printf("%s\n", cmd.str().c_str() );



		}
		
		
	}
}

void create_table_minimal_test_vectors(){


	db_command("drop table minimal_vectors;");
	db_command( "create table minimal_vectors (vector_id Integer, variable varchar(50), hint varchar(50), value varchar(50));" );

}

vector< map<string, string> > vector_of_test_vectors(){

	vector<map<string, string> > ret;

	vector<FreeVariableInfo> free_variables = get_free_variables();
	set<vector<string> > test_vectors = minimal_vectors();

	if(test_vectors.size())
		assert( free_variables.size() == test_vectors.begin()->size() );

	for( set<vector<string> >::iterator it = test_vectors.begin(); it != test_vectors.end(); it++ ){
		map<string, string> mapa;
		for ( unsigned int i = 0; i < free_variables.size(); i++) {
			string var_name = free_variables[i].name;
			string value = (*it)[i];

			mapa[var_name] = value;
		}
		ret.push_back(mapa);
	}

	return ret;

}

string get_position(string name){


	stringstream cmd;
	cmd << "cd " << tmp_dir() << "; echo 'select position from variables where name = \"" << name << "\" limit 1;' | sqlite3 database.db";

	char ret[SIZE_STR];
	FILE *fp = popen(cmd.str().c_str(), "r");
	fscanf(fp, "%s", ret);
	pclose(fp);

	return string(ret);
	
}

vector<FreeVariableInfo> get_free_variables(){

	stringstream cmd;

	cmd.str("");

	if(get_project_path() != "")
		cmd << "cd " << get_project_path() << ";";

	cmd << "echo 'select name,type,position from variables group by name;' | sqlite3 " << tmp_file("database.db");

	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<FreeVariableInfo> ret_vector;
	
	fp = popen(cmd.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL){
		ret[strlen(ret) - 1 ] = 0;

		vector<string> tokens = tokenize(string(ret), "|");

		string name = tokens[0];
		string type = tokens[1];
		string position = tokens[2];

		FreeVariableInfo fvi = {name, type, position};

		ret_vector.push_back(fvi);

	}
	
	pclose(fp);

	return ret_vector;

}

void gen_file_free_variables(){


	vector<FreeVariableInfo> ret_vector = get_free_variables();

	vector<string> outfile;
	for( vector<FreeVariableInfo>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		outfile.push_back( it->name + " " + it->type + " " + it->position );
	}

	string filename;

	filename = tmp_file("free_variables");

	FILE* file = fopen(filename.c_str(), "w");

	for( vector<string>::iterator it = outfile.begin(); it != outfile.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);

}

set<vector<string> > minimal_vectors(){

	// Get results from database
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;

	if(get_project_path() != "")
		command << "cd " << get_project_path() << ";";


	command << "echo 'select name,value,problem_id from results where is_free;' | sqlite3 " << tmp_file("database.db");
	fp = popen(command.str().c_str(), "r");
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	pclose(fp);


	// Get the names
	set<string> names;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		string name = tokens[0];
		names.insert(name);
	}

	
	// For each problem, a relation between name of variable and value
	map< int, map<string, string> > values;
	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		string name = tokens[0];
		string value = tokens[1];
		int problem_id = stoi(tokens[2]);
		values[problem_id][name] = value;
	}

	return pivot(values, names);

	
}

set<vector<string> > pivot( map< int, map<string, string> > values, set<string> names ){

	// Change "" to X
	debug && printf("\e[31m Map \e[0m\n");
	for( map<int,map<string, string> >::iterator it = values.begin(); it != values.end(); it++ ){
		for( set<string>::iterator name = names.begin(); name != names.end(); name++ ){
			if( it->second[*name] == "" ) it->second[*name] = "X";
			debug && printf(" %s ", it->second[*name].c_str() );
		}
		debug && printf("\n");
		
	}

	// Transform to a set of vectors
	set<vector<string> > values_set;
	for( map<int,map<string, string> >::iterator it = values.begin(); it != values.end(); it++ ){
		vector<string> insert_vec;
		for( set<string>::iterator name = names.begin(); name != names.end(); name++ ){
			insert_vec.push_back( it->second[*name].c_str() );
		}
		values_set.insert(insert_vec);
	}

	debug && printf("\e[31m Set \e[0m\n");
	for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
		vector<string> v = *it;
		for( vector<string>::iterator it2 = v.begin(); it2 != v.end(); it2++ ){
			debug && printf("%s  ", it2->c_str());
		}
		debug && printf("\n");
	}
	



	// Delete tests that are covered by another
	
	int prev_size, size;

	while(true){

		int prev_size = values_set.size();

		set<vector<string> > to_insert;
		set<vector<string> > to_remove;

		debug && printf("\e[31m Prunning iteration \e[0m\n");








		debug && printf("\e[32m names \e[0m\n");
		for( set<string>::iterator it = names.begin(); it != names.end(); it++ ){
			debug && printf("%s ", it->c_str());
		}
		debug && printf("\n\e[32m values \e[0m\n");
		for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
			vector<string> row = *it;
			for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
				debug && printf("%s  ", it2->c_str() );
			}
			debug && printf("\n");
		}

		for( set<vector<string> >::iterator v1 = values_set.begin(); v1 != values_set.end(); v1++ ){
			for( set<vector<string> >::iterator v2 = values_set.begin(); v2 != values_set.end(); v2++ ){


				if( *v1 == *v2 ) continue;

				if( !dontcares(*v1) ){
					if(debug){ printf("\e[34m Insert nodc \e[0m"); printvector( *v1 ); }
					to_insert.insert(*v1);
				}

				if( dontcares(*v1) || dontcares(*v2) ){

					if(debug){printf("\e[31m v1 \e[0m "); printvector(*v1);}
					if(debug){printf("\e[31m v2 \e[0m "); printvector(*v2);}

					if( covers_bool(*v1, *v2) ){

						to_remove.insert(*v1);
						to_remove.insert(*v2);
						to_insert.insert( covers(*v1, *v2) );

						if(debug){ printf("\e[34m remove \e[0m "); printvector(*v1); }
						if(debug){ printf("\e[34m remove \e[0m "); printvector(*v2); }
						if(debug){ printf("\e[34m Insert  \e[0m"); printvector( covers(*v1, *v2) ); }

					}

				}

			}

		}

		debug && printf("values_set.size() %lu\n", values_set.size());
		debug && printf("toremove.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_remove.begin(); it != to_remove.end(); it++ ){
			if(debug){ printf("remove "); printvector(*it); }
			values_set.erase( values_set.find(*it) );
		}

		debug && printf("toinsert.size %lu\n", to_insert.size() );
		for( set<vector<string> >::iterator it = to_insert.begin(); it != to_insert.end(); it++ ){
			if(debug){ printf("insert "); printvector(*it); }
			values_set.insert( *it );
		}

		debug && printf("\n\e[32m values \e[0m\n");
		for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
			vector<string> row = *it;
			for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
				debug && printf("%s  ", it2->c_str() );
			}
			debug && printf("\n");
		}

		int size = values_set.size();

		if( size == prev_size ) break;
	}

	set<vector<string> > values_set2;
	for( set<vector<string> >::iterator it = values_set.begin(); it != values_set.end(); it++ ){
		vector<string> vect = *it;
		vector<string> vect2;
		for( vector<string>::iterator it2 = vect.begin(); it2 != vect.end(); it2++ ){
			if(*it2 == "X")
				vect2.push_back("0");
			else
				vect2.push_back(*it2);
		}
		values_set2.insert(vect2);
		
	}

	return values_set2;

}

bool dontcares( vector<string> v ){

	for( vector<string>::iterator it = v.begin(); it != v.end(); it++ ){
		if( *it == "X" )
			return true;
	}

	return false;

}

bool covers_bool( vector<string> v1, vector<string> v2 ){

	debug && printf("\e[31m coversbool \e[0m\n");
	for( vector<string>::iterator it = v1.begin(); it != v1.end(); it++ ){
		debug && printf("%s ", it->c_str() );
	}
	debug && printf(" -- ");
	for( vector<string>::iterator it = v2.begin(); it != v2.end(); it++ ){
		debug && printf("%s ", it->c_str() );
	}
	
	
	for ( unsigned int i = 0; i < v1.size(); i++) {
		//printf("%s %s ", v1[i].c_str(), v2[i].c_str() );
		if( v1[i] != v2[i] && v1[i] != "X" && v2[i] != "X" ){
			debug && printf("not cover\n"); //getchar();
			return false;
		}
	}

	debug && printf("cover\n"); //getchar();

	return true;
}

vector<string> covers( vector<string> v1, vector<string> v2 ){

	vector<string> ret;


	//for( vector<string>::iterator it = v1.begin(); it != v1.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	//printf(" -- ");
	//for( vector<string>::iterator it = v2.begin(); it != v2.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	
	
	for ( unsigned int i = 0; i < v1.size(); i++) {
		/*if( v1[i] == "X" && v2[i] == "X" ){*/
			//ret.push_back( "0" );
		/*} else*/ if( v1[i] == "X" ){
			ret.push_back( v2[i] );
		} else if( v2[i] == "X" ){
			ret.push_back( v1[i] );
		} else {
			if( v1[i] != v2[i] ){printf("ERROR\n"); exit(0);}
			ret.push_back( v1[i] );
		}

	}

	//printf(" -- ");
	//for( vector<string>::iterator it = ret.begin(); it != ret.end(); it++ ){
		//printf("%s ", it->c_str() );
	//}
	//printf("\n"); //getchar();

	return ret;

}

void gen_file_vectors(){

	set<vector<string> > vectors = minimal_vectors();

	vector<string> output_file;
	for( set<vector<string> >::iterator it = vectors.begin(); it != vectors.end(); it++ ){
		vector<string> vect = *it;

		string line;
		for( vector<string>::iterator it2 = vect.begin(); it2 != vect.end(); it2++ ){
			line += *it2 + " ";
		}
		
		output_file.push_back(line);
	}


	string filename;

	filename = tmp_file("vectors");

	FILE* file = fopen( filename.c_str(), "w");
	for( vector<string>::iterator it = output_file.begin(); it != output_file.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
	

}

void show_test_vectors(){

	//db_command(".mode columns\\n.width 6 30 5\\n.headers on\\nselect * from minimal_vectors;");
	
	stringstream command;

	command << "(";

	command << "cd " << tmp_dir() << "; ";

	command << "echo '" << ".mode columns\\n.width 6 20 30 5\\n.headers on\\nselect * from minimal_vectors;" << "' | sqlite3 " << tmp_file("database.db");

	command << ")";
	
	int ret = system(command.str().c_str() );

}

char get_argv_char(int testvector, int i){

	stringstream command;
	FILE *fp;
	char ret[SIZE_STR];

	command.str("");
	command << "cd " << tmp_dir() << "; echo 'select value from minimal_vectors where vector_id=" << testvector << " and hint=\"main_register_argvs+" << i << "\";' | sqlite3 database.db";
	fp = popen(command.str().c_str(), "r");
	fscanf(fp, "%s", ret);
	pclose(fp);

	//printf("%s ", ret);

	if(string(ret) == "")
		return 0;
	else
		return stoi(ret);

}

void show_argvs(){

	int num_vectors;
	int max_size;
	stringstream command;
	FILE *fp;
	char ret[SIZE_STR];

	command.str("");
	command << "cd " << tmp_dir() << "; echo 'select count(distinct vector_id) from minimal_vectors;' | sqlite3 database.db";
	fp = popen(command.str().c_str(), "r");
	fscanf(fp, "%d", &num_vectors);
	pclose(fp);

	string argvs_str = cmd_option_str("sym_argvs");
	string max_size_each_s = tokenize(argvs_str, " ")[2];
	string max_size_s = tokenize(argvs_str, " ")[1];
	max_size = stoi(max_size_s) * stoi(max_size_each_s) + stoi(max_size_s);


	for ( unsigned int testvector = 0; testvector < num_vectors; testvector++) {

		printf("Testcase %3d : ", testvector);
		for ( unsigned int i = 0; i < max_size; i++) {
			
			char argv_char = get_argv_char(testvector, i);
			
			if((unsigned char)argv_char <  32){ printf("\e[1;37m\\%X\e[0m", (unsigned char)argv_char); continue; }
			if((unsigned char)argv_char > 126){ printf("\e[1;37m\\%X\e[0m", (unsigned char)argv_char); continue; }

			printf("%c", argv_char);

		}
		printf("\n");
	}

}

