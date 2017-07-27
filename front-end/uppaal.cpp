/*
 * =====================================================================================
 * /
 * |     Filename:  uppaal.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/11/2014 04:43:06 PM
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

#include "uppaal.h"
#include <stdio.h>
#include <math.h>

// For kactus comparison

#include <stdlib.h>
#include <libxml/xmlmemory.h>
#include <libxml/parser.h>
#include <string>
#include <vector>
#include <fstream>
#include <iostream>


#define XNAME_TEMPLATE 5
#define YNAME_TEMPLATE 5
#define XLOCATION 200
#define YLOCATION 200
#define XLABELGUARD 100
#define YLABELGUARD 100
#define ID_LOCATION_INICIAL "start"


/**
* Function to output semaphore definitions and functions in uppaal
**/
void outputSemaphoreFunctions(FILE *file){

	//fprintf(file,"typedef struct {\n");
	//fprintf(file,"    int val_init;\n");
	//fprintf(file,"    int value;\n");
	//fprintf(file,"}Semaphore;\n\n");
	//fprintf(file,"//WAIT\n");
	//fprintf(file,"int lock_sem(Semaphore s){\n");
	//fprintf(file,"    if(s.value &gt; 0){\n");
	//fprintf(file,"        s.value--;\n");
	//fprintf(file,"        return 1;\n");
	//fprintf(file,"    }\n");
	//fprintf(file,"    return 0;\n");
	//fprintf(file,"}\n\n");
	//fprintf(file,"//SIGNAL\n");
	//fprintf(file,"int unlock_sem(Semaphore s){\n");
	//fprintf(file,"    if(s.value &lt; s.val_init){\n");
	//fprintf(file,"        s.value++;\n");
	//fprintf(file,"    }\n");
	//fprintf(file,"    return 0;\n");
	//fprintf(file,"}\n");

	fprintf(file,"typedef struct {\n");
	fprintf(file,"    int val_init;\n");
	fprintf(file,"    int value;\n");
	fprintf(file,"}Semaphore;\n\n");
	fprintf(file, "//WAIT\n");
	fprintf(file, "int lock_sem(Semaphore &amp;s){\n");
	fprintf(file, "    if(s.value >= s.val_init){\n");
	fprintf(file, "        s.value++;\n");
	fprintf(file, "        return 1;\n");
	fprintf(file, "    }\n");
	fprintf(file, "    s.value++;\n");
	fprintf(file, "    return 0;\n");
	fprintf(file, "}\n");
	fprintf(file, "\n");
	fprintf(file, "//SIGNAL\n");
	fprintf(file, "int unlock_sem(Semaphore &amp;s){\n");
	fprintf(file, "    if(s.value > 0){\n");
	fprintf(file, "        s.value--;\n");
	fprintf(file, "    }\n");
	fprintf(file, "    return 0;\n");
	fprintf(file, "}\n");
	fprintf(file, "\n");
	fprintf(file, "int check_lock_sem(Semaphore s){\n");
	fprintf(file, "    if(s.value >= s.val_init){\n");
	fprintf(file, "        return 1;\n");
	fprintf(file, "    }\n");
	fprintf(file, "    return 0;\n");
	fprintf(file, "}\n");
	fprintf(file, "\n");
	fprintf(file, "//SIGNAL\n");
	fprintf(file, "int check_unlock_sem(Semaphore s){\n");
	fprintf(file, "    return 0;\n");
	fprintf(file, "}\n");

}


string uppaal_type(string forest_type){
	if(forest_type == "Int") return "int"; 
	if(forest_type == "bool") return "bool";
	if(forest_type == "IntegerTyID32") return "int";
	if(forest_type == "SemTyID") return "Semaphore";
	if(forest_type == "Pointer") return "Pointer";

	printf("%s\n", forest_type.c_str());
	assert(0 && "Unknown type");
}

void trim_last_comma(string& expression){
	if(expression[expression.length()-1] == ',') expression = expression.substr(0,expression.length()-1);
}


string uppaal_constant(string forest_constant){
	vector<string> tokens = tokenize(forest_constant, "_");
	if(!tokens.size()) assert(0 && "non-constant format");
	assert(tokens[0] == "constant" && "uppaal_constant of a non_constant");
	return tokens[2];
}

void uppaal_names(string& expression, string function){

	if(cmd_option_bool("no_uppaal_names")) return;

	myReplace(expression, "Z3fn1Pv", "fn1");
	myReplace(expression, "Z2fni", "fn");
	myReplace(expression, "underscore", "_");
	myReplace(expression, "_register_", "_");

}


vector<string> dbcommand(string cmd){

	vector<string> ret;

	stringstream command;
	command.str("");
	command << "echo '" << cmd << "' | sqlite3 " << tmp_file("database.db") << " > " << tmp_file("dbcommand");
	systm(command.str());


	ifstream input(tmp_file("dbcommand").c_str());
	string line;

	while( getline( input, line ) ) {
		ret.push_back(line);
	}

	return ret;

}


/**
* Function that declares global data
**/
void uppaalDeclareGlobalVariables(FILE *file){

	// read variables from global variables table
	int i=0;
	stringstream command;
	string output;
	fprintf(file,"<declaration>\n");

	outputSemaphoreFunctions(file);

	vector<string> variables = dbcommand("select distinct name,init,type from uppaal_variables WHERE name LIKE \"global_\%\";");

	for( vector<string>::iterator it = variables.begin(); it != variables.end(); it++ ){
		string line = *it;
		myReplace(line, "|", "| ");
		string name = tokenize(line,"|")[0];
		string init = tokenize(line,"|")[1].substr(1);
		string type = tokenize(line,"|")[2].substr(1);

		//bool isSemaphore = (name == "global_a")|(name == "global_b")|(name == "global_c");
		bool isSemaphore = uppaal_type(type) == "Semaphore";
		
		if(isSemaphore){
			fprintf(file,"Semaphore %s = {1,0};\n", name.c_str());
		}else{
			if(init != "")
				fprintf(file, "%s %s = %s;\n", uppaal_type(type).c_str(), name.c_str(), uppaal_constant(init).c_str());
			else 
				fprintf(file, "%s %s;\n", uppaal_type(type).c_str(), name.c_str());
		}
	}
	fprintf(file,"</declaration>\n");
}



bool is_in(string var, string expr){
	if(expr.find(" " + var + " ") != string::npos) return true;
	if(expr.find("(" + var + " ") != string::npos) return true;
	if(expr.find(" " + var + ")") != string::npos) return true;
	if(expr.length() >= var.length() && expr.substr(0, var.length()) == var && expr.substr(var.length(),1) == " ") return true;
	if(expr.length() >= var.length() && expr.substr(expr.length() - var.length()) == var) return true;

	return false;
}

set<string> unused_variables_set;

bool used(string var){
	if(var.find("main") != string::npos) return false;
	if(var.find("argument") != string::npos) return false;
	if(var.find("underscoreargsunderscoreaddr") != string::npos) return false;
	if(var.find("underscoreretval") != string::npos) return false;
	if(var.find("_retval") != string::npos) return false;
	if(var.find("_addr") != string::npos) return false;
	if(var.find("underscoreaddr") != string::npos) return false;
	//if(var.find("_register_") != string::npos ) return true;
	if(var.find("global_") != string::npos) return true;
	if(unused_variables_set.find(var) == unused_variables_set.end()) return true;
	else return false;
}

void unused_variables(){

	if(cmd_option_bool("no_uppaal_simplify")) return;

	vector<string> variables  = dbcommand("select distinct name from uppaal_variables;");
	vector<string> assigns    = dbcommand("select distinct assigns from uppaal;");
	vector<string> conditions = dbcommand("select distinct conditions from uppaal;");
	map<string, set<string> > is_in_left_right;

	for( vector<string>::iterator it = variables.begin(); it != variables.end(); it++ ){
		string variable = *it;
		for( vector<string>::iterator it2 = assigns.begin(); it2 != assigns.end(); it2++ ){
			string assign_row = *it2;

			//printf("checking for variable %s in assigns %s\n", variable.c_str(), assign_row.c_str());

			vector<string> assigns_simple = tokenize(assign_row, ",");
			for( vector<string>::iterator it3 = assigns_simple.begin(); it3 != assigns_simple.end(); it3++ ){
				string assign_simple = *it3;
				string right = assign_simple.substr(assign_simple.find("=")+1);
				string left  = assign_simple.substr(0, assign_simple.find("="));

				//printf("checking for variable %s in assign %s\n", variable.c_str(), assign_simple.c_str());
				
				if(left == variable) is_in_left_right[variable].insert("left");
				if(is_in(variable, right)) is_in_left_right[variable].insert("right");
			}
			
		}

		for( vector<string>::iterator it4 = conditions.begin(); it4 != conditions.end(); it4++ ){
			if(is_in(variable, *it4)) is_in_left_right[variable].insert("right");
		}
	}

	for( vector<string>::iterator it = variables.begin(); it != variables.end(); it++ ){
		//if(is_in_left_right[*it].find("left") != is_in_left_right[*it].end() && is_in_left_right[*it].find("right") == is_in_left_right[*it].end())
		if(is_in_left_right[*it].find("right") == is_in_left_right[*it].end())
			unused_variables_set.insert(*it);
	}
	
}



void uppaal_local_declarations(string function, FILE* file){

	fprintf(file,"<declaration>\n");
	fprintf(file,"//local variables for conds\n");


	vector<string> local_variables = dbcommand("select distinct type,name from uppaal_variables where name not like \"global\%\%\";");


	for( vector<string>::iterator it2 = local_variables.begin(); it2 != local_variables.end(); it2++ ){

		string type = tokenize(*it2, "|")[0];
		string name = tokenize(*it2, "|")[1];


		if(used(name)){
			uppaal_names(name, function);
			fprintf(file, "%s %s;\n", uppaal_type(type).c_str(), name.c_str());
		}
	}
	fprintf(file,"</declaration>\n");
}

map<string, pair<float, float> > generate_graph_layout(){

	map<string, pair<float, float> > ret;

	FILE* file_aux = fopen(tmp_file("dotlayout").c_str(), "w");

	vector<string> transitions = dbcommand("select distinct src,dst from uppaal;");

	fprintf(file_aux, "digraph G{\n");

	for( vector<string>::iterator it = transitions.begin(); it != transitions.end(); it++ ){
		string src = tokenize(*it, "|")[0];
		string dst = tokenize(*it, "|")[1];
		fprintf(file_aux, "%s->%s\n", src.c_str(), dst.c_str());
	}
	

	fprintf(file_aux, "}\n");

	fclose(file_aux);


	systm("cat " + tmp_file("dotlayout") + " | dot -Tplain | grep node | awk '{print $2 \" \" $3 \" \" $4}' > " + tmp_file("layout"));

	ifstream input(tmp_file("layout").c_str());
	string line;
	
	while( getline( input, line ) ) {
		string name = tokenize(line, " ")[0];
		string x    = tokenize(line, " ")[1];
		string y    = tokenize(line, " ")[2];
		ret[name] = pair<float,float>(stof(x), stof(y));
	}
	
	
	return ret;

}



map<pair<string, string>, vector<pair<float, float> > > generate_edge_layout(){


	map<string, pair<float, float> > graph_layout = generate_graph_layout();

	map<pair<string, string>, vector<pair<float, float> > > ret;
	vector<string> transitions;

	map<pair<string,string>, int> transitions_num;
	transitions = dbcommand("select distinct * from uppaal;");
	for( vector<string>::iterator it = transitions.begin(); it != transitions.end(); it++ ){
		string src = tokenize(*it, "|")[0];
		string dst = tokenize(*it, "|")[1];
		transitions_num[pair<string,string>(src,dst)]++;
	}


	transitions = dbcommand("select distinct src,dst from uppaal;");
	for( vector<string>::iterator it = transitions.begin(); it != transitions.end(); it++ ){
		string src = tokenize(*it, "|")[0];
		string dst = tokenize(*it, "|")[1];
		float x1 = graph_layout[src].first;
		float y1 = graph_layout[src].second;
		float x2 = graph_layout[dst].first;
		float y2 = graph_layout[dst].second;
		if(transitions_num[pair<string,string>(src,dst)] > 2){
			float angle = atan2(y2-y1, x2-x1) + 90.0*3.1416/180.0;
			int ntr = transitions_num[pair<string, string>(src,dst)];
			for ( int i = 0,j=-ntr/2; i < ntr; i++,j++) {
				float x = x1+(x2-x1)/2.0;
				float y = y1+(y2-y1)/2.0;
				x += 0.1*j*cos(angle);
				y += 0.1*j*sin(angle);
				ret[pair<string,string>(src,dst)].push_back(pair<float,float>(x,y));
			}
		}
	}

	
	return ret;

}





void uppaal_coords(float* x, float* y){
	*x = - cmd_option_float("uppaal_scale") * 100.0*( *x );
	*y = - cmd_option_float("uppaal_scale") * 100.0*( *y );
}

void uppaal_locations(string function, FILE* file){

	map<string, pair<float, float> > graph_layout = generate_graph_layout();

	stringstream command;
	command << "select distinct src from uppaal union ";
	command << "select distinct dst from uppaal;";
	vector<string> locations = dbcommand(command.str());

	for( vector<string>::iterator it3 = locations.begin(); it3 != locations.end(); it3++ ){

		string urgent = tokenize(*it3,"_")[1] == "cond"?"<urgent/>":"";
		
		float x = graph_layout[*it3].first;
		float y = graph_layout[*it3].second;
		uppaal_coords(&x, &y);


		if(cmd_option_bool("location_names"))
			fprintf(file,"<location id=\"%s\" x=\"%.0f\" y=\"%.0f\"><name>%s</name></location>%s\n",it3->c_str(),x,y,it3->c_str(), urgent.c_str());
		else
			fprintf(file,"<location id=\"%s\" x=\"%.0f\" y=\"%.0f\"></location>%s\n",it3->c_str(),x,y, urgent.c_str());
	}

	fprintf(file,"<init ref=\"%s_start\"/>\n",function.c_str());

}

string uppaal_condition(string input){

	myReplace(input, "&", "&amp;");
	myReplace(input, "<", "&lt;");
	myReplace(input, ">", "&gt;");
	myReplace(input, "\"", "&quot;");
	myReplace(input, "'", "&apos;");
	myReplace(input, "#", "!=");

	return input;
}

void remove_unused_assigns(string& assigns){
	string ret;
	vector<string> tokens = tokenize(assigns, ",");
	for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
		string assign = *it;
		string left  = assign.substr(0, assign.find("="));
		string right = assign.substr( assign.find("=")+1);
		if(used(left))
			ret = ret + assign + ",";
	}
	assigns = ret;
	
}

void uppaal_transitions(string function, FILE* file){

	map<string, pair<float, float> > graph_layout = generate_graph_layout();
	map<pair<string, string>, vector<pair<float, float> > > edge_layout = generate_edge_layout();

	vector<string> transitions = dbcommand("select distinct * from uppaal;");
	map<pair<string,string>, int> distinct_edge_count;

	for( vector<string>::iterator it = transitions.begin(); it != transitions.end(); it++ ){

		string line = *it;
		myReplace(line, "|", "| ");
		string src = tokenize(line, "|")[0];
		string dst = tokenize(line, "|")[1].substr(1);
		string cnd = tokenize(line, "|")[2].substr(1);
		string sem = tokenize(line, "|")[3].substr(1);
		string lck = tokenize(line, "|")[4].substr(1);
		string ass = tokenize(line, "|")[5].substr(1);
		string guard;

		uppaal_names(ass, function);

		if(sem != "" && cnd != ""){
			guard = "check_" + lck + "_sem(" + sem + ")==0" + cnd;
			ass += "," + lck + "_sem(" + sem + ")" + cnd;
		} else if(sem != ""){
			guard = "check_" + lck + "_sem(" + sem + ")==0";
			ass += "," + lck + "_sem(" + sem + ")" + cnd;
		} else if(cnd != ""){
			guard = cnd;
		}

		if(ass.substr(0,1) == ",") ass = ass.substr(1);

		uppaal_names(guard, function);
		guard = uppaal_condition(guard);

		float x_guard   = 0.5*(graph_layout[src].first  + graph_layout[dst].first)  - 0.1;
		float y_guard   = 0.5*(graph_layout[src].second + graph_layout[dst].second) + 0.1;
		float x_assigns = 0.5*(graph_layout[src].first  + graph_layout[dst].first)  - 0.1;
		float y_assigns = 0.5*(graph_layout[src].second + graph_layout[dst].second) - 0.1;
		uppaal_coords(&x_guard, &y_guard);
		uppaal_coords(&x_assigns, &y_assigns);

		fprintf(file, "<transition>\n");
		fprintf(file, "<source ref=\"%s\"/>\n", src.c_str());
		fprintf(file, "<target ref=\"%s\"/>\n", dst.c_str());
		fprintf(file, "<label kind=\"guard\" x=\"%.0f\" y=\"%.0f\">%s</label>\n",x_guard,y_guard, guard.c_str());
		fprintf(file, "<label kind=\"assignment\" x=\"%.0f\" y=\"%.0f\">%s</label>\n", x_assigns, y_assigns, ass.c_str());
		if( edge_layout[pair<string, string>(src,dst)].size() > 1 ){
			pair<float,float> posnail = edge_layout[pair<string, string>(src,dst)][distinct_edge_count[pair<string,string>(src,dst)]];
			float x = posnail.first;
			float y = posnail.second;
			uppaal_coords(&x, &y);
			fprintf(file, "<nail x=\"%.0f\" y=\"%.0f\"/>\n", x, y);
			distinct_edge_count[pair<string,string>(src,dst)]++;
		}
		fprintf(file, "</transition>\n");

	}
}


void uppaalTemplates(FILE *file){


	vector<string> functions = dbcommand("SELECT distinct src from uppaal WHERE src LIKE \"\%_start\";");

	for( vector<string>::iterator it = functions.begin(); it != functions.end(); it++ ){
		string function = tokenize(*it, "_")[0];
		fprintf(file,"<template>\n");
		fprintf(file,"<name x=\"%d\" y=\"%d\">%s</name>\n",XNAME_TEMPLATE,YNAME_TEMPLATE, function.c_str());


		uppaal_local_declarations(function, file);

		uppaal_locations(function, file);

		uppaal_transitions(function, file);


		fprintf(file,"</template>\n");
		fprintf(file,"<system>system %s;</system>\n", function.c_str());

	}

	fprintf(file,"</nta>\n");


}


/**
* Function to generate uppaal xml file from previous database tables
**/
void generateUppaalCode(){
	FILE *file;
	file =fopen("uppaal.xml","w");
	fprintf(file, "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n");
	fprintf(file,"<nta>\n");
	uppaalDeclareGlobalVariables(file);
	uppaalTemplates(file);
	fclose(file);
}

inline bool operator<(const UppaalRow& lhs, const UppaalRow& rhs) {
	return lhs.src + lhs.dst + lhs.conditions + lhs.semaphore + lhs.lockunlock + lhs.assigns < 
	       rhs.src + rhs.dst + rhs.conditions + rhs.semaphore + rhs.lockunlock + rhs.assigns;
}

void reinsert_row(string src, string dst, string cnd, string sem, string lck, string ass){

	stringstream command;
	command	<< "insert into uppaal values (";
	command << "\"" << src << "\",";
	command << "\"" << dst << "\",";
	command << "\"" << cnd << "\",";
	command << "\"" << sem << "\",";
	command << "\"" << lck << "\",";
	command << "\"" << ass << "\"";
	command	<< ");";

	//printf("%s\n", command.str().c_str());
	dbcommand(command.str());
}

void simplify_uppaal_table(){

	unused_variables();
	for( set<string>::iterator it = unused_variables_set.begin(); it != unused_variables_set.end(); it++ ){
		printf("unused_variable %s\n", it->c_str());
	}

	vector<string> table = dbcommand("select * from uppaal;");

	set<UppaalRow> uppaal_table;
	for( vector<string>::iterator it = table.begin(); it != table.end(); it++ ){
		string line = *it;
		myReplace(line, "|", "| ");
		string src = tokenize(line, "|")[0];
		string dst = tokenize(line, "|")[1].substr(1);
		string cnd = tokenize(line, "|")[2].substr(1);
		string sem = tokenize(line, "|")[3].substr(1);
		string lck = tokenize(line, "|")[4].substr(1);
		string ass = tokenize(line, "|")[5].substr(1);


		remove_unused_assigns(ass);
		ass = uppaal_condition(ass);
		trim_last_comma(ass);


		UppaalRow row = {src, dst, cnd, sem, lck, ass};

		uppaal_table.insert(row);
	}

	dbcommand("delete from uppaal;");

	for( set<UppaalRow>::iterator it = uppaal_table.begin(); it != uppaal_table.end(); it++ ){
		string src = it->src;
		string dst = it->dst;
		string cnd = it->conditions;
		string sem = it->semaphore;
		string lck = it->lockunlock;
		string ass = it->assigns;


		reinsert_row(src, dst, cnd, sem, lck, ass);
	}
	

	

}

void generate_uppaal_model(){

	stringstream cmd;
	cmd.str("");
	cmd << "rm -rf " << tmp_file("*");
	systm(cmd.str().c_str());


	make_initial_bc();
	clean_tables();
	dump_forced_free_hints();
	dump_forced_free_vars();


	string llvm_path = cmd_option_str("llvm_path");
	string base_path = cmd_option_str("base_path");
	string output_file = cmd_option_str("output_file");

	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_sep < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_extractfn < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());


	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file-3.bc > file-4.bc";
	systm(cmd.str().c_str());

	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-4.bc > file-5.bc";
	systm(cmd.str().c_str());





	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestConcurrency.so -conc_changesync_2 < file-5.bc > file-6.bc";
	systm(cmd.str().c_str());

	// From .bc to .s
	cmd.str("");
	cmd << "llc file-6.bc -o file-6.s";
	systm(cmd.str().c_str());

	// From .s to .o
	cmd.str("");
	cmd << "gcc -c file-6.s -o file-6.o";
	systm(cmd.str().c_str());

	// link
	cmd.str("");
	cmd << "g++ file-6.o " << base_path << "/lib/forest.a" << " -lpthread -ldl -lrt -o " << output_file;
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "./" << output_file;
	systm(cmd.str().c_str());



	simplify_uppaal_table();
	
	db_command_visible(".mode column\n.headers on\n.width 10 10 20 8 6 100\nselect distinct * from uppaal;");
	db_command_visible(".mode column\n.headers on\n.width 50 20 30\nselect distinct * from uppaal_variables;");
	

	generateUppaalCode();
}


void insert_xml_row(string nameT, string nameV, string type, string action){

	stringstream command;
	command	<< "insert into check_xml values (";
	command << "\"" << nameT << "\",";
	command << "\"" << nameV << "\",";
	command << "\"" << type << "\",";
	command << "\"" << action << "\"";
	command	<< ");";

	dbcommand(command.str());
}

// Only taken into account valid dependencies. Si en el futuro se quieren tener en cuenta más añadirlas
// tanto aqui como en check_read_write
bool valid_dependency(std::string type)
{
	if((0 == type.compare("Semaphore")) || (0 == type.compare("SemaphoreIte")))
	{
		return true;
	}
	else if((0 == type.compare("Mutex")) || (0 == type.compare("MutexIte")))
	{
		return true;
	}
	else if((0 == type.compare("ThreadBarrier")) || (0 == type.compare("ThreadBarrierIte")))
	{
		return true;
	}
	else if((0 == type.compare("SharedVariable")) || (0 == type.compare("SharedVariableIte")))
	{
		return true;
	}
	else if((0 == type.compare("ConditionalVariable")) || (0 == type.compare("ConditionalVariableIte")))
	{
		return true;
	}
	else
	{
		return false;
	}
}
void fill_table_xml(){
	std::string input_file = cmd_option_str("filexml");
	std::vector<info_thr_temp_t> info_threads_dependencies;
	info_thr_temp_t info_thr_temp;
	info_dep_temp_t info_dep_temp;
	xmlDocPtr doc;
	xmlNodePtr cur,curProcess,curThread,curThreadDependency,curDependency,curDependencyProp,curGetDepProp;
	char *text,*ite_size;
	int NumberProcesses,NumberThreads,NumberDependencies,NumberProperties,dimensions,index,char_index,last_index;
	bool check_range;
	bool check,func_on_list;
	char *func_name_tmp_file;
	char buffer[100];
	std::vector<std::string> to_ite;
	std::string from_ite;
	std::string to_ite_tmp;
	buffer[99] = '\0';
	doc = xmlParseFile(input_file.c_str());
	//Dependency rw;
	if (doc == NULL )
	{
		printf("Document %s not parsed successfully. \n", input_file.c_str());
		exit (-1);
	}
	cur = xmlDocGetRootElement(doc);
	if (cur == NULL) 
	{
		printf("empty document\n");
		xmlFreeDoc(doc);
		exit(-1);
	}
	if (xmlStrcmp(cur->name, (const xmlChar *) "DependenciesModel"))
	{
		printf("document of the wrong type, root node != DependenciesModel\n");
		xmlFreeDoc(doc);
		return;
	}
	cur = xmlFirstElementChild(cur);
	//Get thread names
	while (xmlStrcmp(cur->name, (const xmlChar *) "Processes")) 
	{
		cur = xmlNextElementSibling(cur);
		if(cur == NULL)
		{
			printf("Error: tag \"Processes\" not found\n");
			xmlFreeDoc(doc);
			exit( -1);
		}
	}
	NumberProcesses = xmlChildElementCount(cur);
	curProcess = xmlFirstElementChild(cur);
	for(int i=0;i<NumberProcesses;i++)
	{
		if(xmlStrcmp(curProcess->name, (const xmlChar *) "Process"))
		{
			printf("Error: expected tag \"Process\"\n");
			xmlFreeDoc(doc);
			exit( -1);
		}
		curThread = xmlFirstElementChild(curProcess);
		while (xmlStrcmp(curThread->name, (const xmlChar *) "Threads")) 
		{
			curThread = xmlNextElementSibling(curThread);
			if(curThread == NULL)
			{
				printf("Error: tag \"Threads\" not found\n");
				xmlFreeDoc(doc);
				exit( -1);
			}
		}
		NumberThreads = xmlChildElementCount(curThread);
		curThread = xmlFirstElementChild(curThread);
		for(int q=0;q<NumberThreads;q++)
		{
			if(xmlStrcmp(curThread->name, (const xmlChar *) "Thread") && xmlStrcmp(curThread->name, (const xmlChar *) "ThreadIte"))
			{
				printf("Error: expected tag \"Thread\" or \"ThreadIte\"\n");
				xmlFreeDoc(doc);
				exit( -1);
			}
			if(0 == xmlStrcmp(curThread->name, (const xmlChar *) "Thread"))
			{
				curThreadDependency = xmlFirstElementChild(curThread);
				if(xmlStrcmp(curThreadDependency->name, (const xmlChar *) "ThreadId"))
				{
					printf("Error: expected tag \"ThreadId\"\n");
					xmlFreeDoc(doc);
					exit( -1);
				}
				
				text=(char *)xmlNodeGetContent(curThreadDependency);
				if(text == NULL)
				{
					printf("Error: Missed thread name\n");
					xmlFreeDoc(doc);
					exit( -1);
				}
				func_on_list = true;
				if(func_on_list)
				{
					info_thr_temp.name = std::string(text);
					info_thr_temp.number_threads_ite = "none"; 
					curThreadDependency = xmlNextElementSibling(curThreadDependency);
					if(xmlStrcmp(curThreadDependency->name, (const xmlChar *) "ThreadDependencies"))
					{
						printf("Error: expected tag \"ThreadDependencies\"\n");
						xmlFreeDoc(doc);
						exit( -1);
					}
					NumberDependencies = xmlChildElementCount(curThreadDependency);
					curThreadDependency = xmlFirstElementChild(curThreadDependency);
					for(int j=0;j<NumberDependencies;j++)
					{
						curDependency = xmlFirstElementChild(curThreadDependency);
						if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyName"))
						{
							printf("Error: expected tag \"ThreadDependencyName\"\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						text=(char *)xmlNodeGetContent(curDependency);
						if(text == NULL)
						{
							printf("Error: Missed dependency name\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						info_dep_temp.name = std::string(text);
						curDependency = xmlNextElementSibling(curDependency);
						if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyType"))
						{
							printf("Error: expected tag \"ThreadDependencyType\"\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						text=(char *)xmlNodeGetContent(curDependency);
						if(text == NULL)
						{
							printf("Error: Missed dependency type\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						info_dep_temp.type = std::string(text);
						curDependency = xmlNextElementSibling(curDependency);
						if(0 == xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyToIte"))
						{
							text=(char *)xmlNodeGetContent(curDependency);
							if(text == NULL)
							{
								printf("Error: Missed dependency to_ite\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							info_dep_temp.to_ite = std::string(text);
							curDependency = xmlNextElementSibling(curDependency);
							if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyAction"))
							{
								printf("Error: expected tag \"ThreadDependencyAction\"\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							text=(char *)xmlNodeGetContent(curDependency);
							if(text == NULL)
							{
								printf("Error: Missed dependency action\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							info_dep_temp.action = std::string(text);
							
						}
						else if(0 == xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyAction"))
						{
							text=(char *)xmlNodeGetContent(curDependency);
							if(text == NULL)
							{
								printf("Error: Missed dependency action\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							info_dep_temp.action = std::string(text);
							info_dep_temp.to_ite = "\0";
						}
						else
						{
							printf("Error: expected tag \"ThreadDependencyAction\"\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						if(valid_dependency(info_dep_temp.type))
						{
							info_thr_temp.info_dependencies.push_back(info_dep_temp);
						}
						curThreadDependency = xmlNextElementSibling(curThreadDependency);
					}
					info_threads_dependencies.push_back(info_thr_temp);
					info_thr_temp.info_dependencies.clear();
				}
			// Fin comprobacion dsi la funcion esta en el vector de funciones
			}
			else
			{
				curThreadDependency = xmlFirstElementChild(curThread);
				if(xmlStrcmp(curThreadDependency->name, (const xmlChar *) "ThreadIteId"))
				{
					printf("Error: expected tag \"ThreadIteId\"\n");
					xmlFreeDoc(doc);
					exit( -1);
				}
				
				text=(char *)xmlNodeGetContent(curThreadDependency);
				if(text == NULL)
				{
					printf("Error: Missed thread name\n");
					xmlFreeDoc(doc);
					exit( -1);
				}
				func_on_list = true;
				if(func_on_list)
				{
					info_thr_temp.name = std::string(text);
					curThreadDependency = xmlNextElementSibling(curThreadDependency);
					if(xmlStrcmp(curThreadDependency->name, (const xmlChar *) "NumberThreadsIte"))
					{
						printf("Error: expected tag \"NumberThreadsIte\"\n");
						xmlFreeDoc(doc);
						exit( -1);
					}
					text=(char *)xmlNodeGetContent(curThreadDependency);
					info_thr_temp.number_threads_ite =  std::string(text);
					curThreadDependency = xmlNextElementSibling(curThreadDependency);
					if(xmlStrcmp(curThreadDependency->name, (const xmlChar *) "ThreadDependencies"))
					{
						printf("Error: expected tag \"ThreadDependencies\"\n");
						xmlFreeDoc(doc);
						exit( -1);
					}
					NumberDependencies = xmlChildElementCount(curThreadDependency);
					curThreadDependency = xmlFirstElementChild(curThreadDependency);
					for(int j=0;j<NumberDependencies;j++)
					{
						curDependency = xmlFirstElementChild(curThreadDependency);
						if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyName"))
						{
							printf("Error: expected tag \"ThreadDependencyName\"\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						text=(char *)xmlNodeGetContent(curDependency);
						if(text == NULL)
						{
							printf("Error: Missed dependency name\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						info_dep_temp.name = std::string(text);
						curDependency = xmlNextElementSibling(curDependency);
						if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyType"))
						{
							printf("Error: expected tag \"ThreadDependencyType\"\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						text=(char *)xmlNodeGetContent(curDependency);
						if(text == NULL)
						{
							printf("Error: Missed dependency type\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
						info_dep_temp.type = std::string(text);
						curDependency = xmlNextElementSibling(curDependency);
						if(0 == xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyToIte"))
						{
							text=(char *)xmlNodeGetContent(curDependency);
							if(text == NULL)
							{
								printf("Error: Missed dependency to_ite\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							info_dep_temp.to_ite = std::string(text);
							curDependency = xmlNextElementSibling(curDependency);
							if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyFromIte"))
							{
								printf("Error: expected tag \"ThreadDependencyFromIte\"\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							text=(char *)xmlNodeGetContent(curDependency);
							info_dep_temp.from_ite = std::string(text);
							curDependency = xmlNextElementSibling(curDependency);
							if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyAction"))
							{
								printf("Error: expected tag \"ThreadDependencyAction\"\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							text=(char *)xmlNodeGetContent(curDependency);
							info_dep_temp.action = std::string(text);
							
						}
						else if(0 == xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyFromIte"))
						{
							text=(char *)xmlNodeGetContent(curDependency);
							if(text == NULL)
							{
								printf("Error: expected tag \"ThreadDependencyFromIte\"\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							info_dep_temp.from_ite = std::string(text);
							curDependency = xmlNextElementSibling(curDependency);
							if(xmlStrcmp(curDependency->name, (const xmlChar *) "ThreadDependencyAction"))
							{
								printf("Error: expected tag \"ThreadDependencyAction\"\n");
								xmlFreeDoc(doc);
								exit( -1);
							}
							text=(char *)xmlNodeGetContent(curDependency);
							info_dep_temp.action = std::string(text);
							info_dep_temp.to_ite = "\0";
						}
						else
						{
							printf("Error: expected tag \"ThreadDependencyAction\" %s \n",info_dep_temp.name.c_str());
							xmlFreeDoc(doc);
							exit( -1);
						}
						if(valid_dependency(info_dep_temp.type))
						{
							info_thr_temp.info_dependencies.push_back(info_dep_temp);
						}
						curThreadDependency = xmlNextElementSibling(curThreadDependency);
					}
					info_threads_dependencies.push_back(info_thr_temp);
					info_thr_temp.info_dependencies.clear();
				}
			// Fin comprobacion dsi la funcion esta en el vector de funciones
			}

			curThread = xmlNextElementSibling(curThread);
		}
		curProcess = xmlNextElementSibling(curProcess);
	}
	
	//Read dependencies!
	while (xmlStrcmp(cur->name, (const xmlChar *) "Dependencies")) 
	{
		cur = xmlNextElementSibling(cur);
		if(cur == NULL)
		{
			printf("Error: tag \"Dependencies\" not found\n");
			xmlFreeDoc(doc);
			exit( -1);
		}
	}
	NumberDependencies = xmlChildElementCount(cur);
	curDependency = xmlFirstElementChild(cur);
	
	for(int i=0;i<NumberDependencies;i++)
	{
		if(xmlStrcmp(curDependency->name, (const xmlChar *) "Dependency"))
		{
			printf("Error: expected tag \"Dependency\"\n");
			xmlFreeDoc(doc);
			exit( -1);
		}
		curDependencyProp = xmlFirstElementChild(curDependency);
		
		while (xmlStrcmp(curDependencyProp->name, (const xmlChar *) "DependencyID")) 
		{
			curDependencyProp = xmlNextElementSibling(curDependencyProp);
			if(curDependencyProp == NULL)
			{
				printf("Error: tag \"DependencyID\" not found\n");
				xmlFreeDoc(doc);
				exit( -1);
			}
		}
		text=(char *)xmlNodeGetContent(curDependencyProp);
		if(text == NULL)
		{
			printf("Error: Missed dependency id\n");
			xmlFreeDoc(doc);
			exit( -1);
		}
		curDependencyProp = xmlFirstElementChild(curDependency);
		while (xmlStrcmp(curDependencyProp->name, (const xmlChar *) "IteDependencyType")) 
		{
			curDependencyProp = xmlNextElementSibling(curDependencyProp);
			if(curDependencyProp == NULL)
			{
				break;
			}
		}
		ite_size = NULL;
		if(curDependencyProp != NULL)
		{
			curDependencyProp = xmlFirstElementChild(curDependency);
			while (xmlStrcmp(curDependencyProp->name, (const xmlChar *) "DependencyProperties")) 
			{
				curDependencyProp = xmlNextElementSibling(curDependencyProp);
				if(curDependencyProp == NULL)
				{
					printf("Error: tag \"DependencyProperties\" not found\n");
					xmlFreeDoc(doc);
					exit( -1);
				}
			}
			NumberProperties = xmlChildElementCount(curDependencyProp);
			curDependencyProp = xmlFirstElementChild(curDependencyProp);
			for(int q=0;q<NumberProperties;q++)
			{
				curGetDepProp = xmlFirstElementChild(curDependencyProp);
				while (xmlStrcmp(curGetDepProp->name, (const xmlChar *) "DependencyPropertyId")) 
				{
					curGetDepProp = xmlNextElementSibling(curGetDepProp);
					if(curGetDepProp == NULL)
					{
						printf("Error: tag \"DependencyPropertyId\" not found\n");
						xmlFreeDoc(doc);
						exit( -1);
					}
				}
				if(0 == xmlStrcmp(xmlNodeGetContent(curGetDepProp), (const xmlChar *) "ite_size"))
				{
					curGetDepProp = xmlFirstElementChild(curDependencyProp);
					while (xmlStrcmp(curGetDepProp->name, (const xmlChar *) "DependencyPropertyValue")) 
					{
						curGetDepProp = xmlNextElementSibling(curGetDepProp);
						if(curGetDepProp == NULL)
						{
							printf("Error: tag \"DependencyPropertyValue\" not found\n");
							xmlFreeDoc(doc);
							exit( -1);
						}
					}
					ite_size=(char *)xmlNodeGetContent(curGetDepProp);
					if(ite_size == NULL)
					{
						printf("Error: Missed ite_size\n");
						xmlFreeDoc(doc);
						exit( -1);
					}
					break;
				}
				curDependencyProp = xmlNextElementSibling(curDependencyProp);	
			}
		}
		curDependency = xmlNextElementSibling(curDependency);
	}
	

	//INSERCION EN LA BASE DE DATOS!!!
	for(int i = 0; i < info_threads_dependencies.size();i++)
	{
		if(0 == info_threads_dependencies[i].name.compare("main_thread"))
		{
			//NO LO TENGO EN CUENTA
			continue;
		}

		for(int q = 0; q < info_threads_dependencies[i].info_dependencies.size();q++)
		{

			string nameT = info_threads_dependencies[i].name.c_str();
			string nameV = info_threads_dependencies[i].info_dependencies[q].name.c_str();
			string type = info_threads_dependencies[i].info_dependencies[q].type.c_str();
			
			if(0 == info_threads_dependencies[i].info_dependencies[q].action.compare("ReadWrite"))
			{
				
				insert_xml_row(nameT, nameV, type, "Read");
				insert_xml_row(nameT, nameV, type, "Write");
			}else{
				string action = info_threads_dependencies[i].info_dependencies[q].action.c_str();
				insert_xml_row(nameT, nameV, type, action);
			}

		}
		
	}
}

void insert_uppaal_row(string nameT, string nameV, string type, string action){

	stringstream command;
	command	<< "insert into check_uppaal values (";
	command << "\"" << nameT << "\",";
	command << "\"" << nameV << "\",";
	command << "\"" << type << "\",";
	command << "\"" << action << "\"";
	command	<< ");";

	dbcommand(command.str());
}


void inserta_asignamientos(){
	vector<string> assigns    = dbcommand("select distinct assigns from uppaal;");


	for( vector<string>::iterator it2 = assigns.begin(); it2 != assigns.end(); it2++ ){
		string assign_row = *it2;

		vector<string> assigns_simple = tokenize(assign_row, ",");
		for( vector<string>::iterator it3 = assigns_simple.begin(); it3 != assigns_simple.end(); it3++ ){
			string assign_simple = *it3;
			string right = assign_simple.substr(assign_simple.find("=")+1);
			string left  = assign_simple.substr(0, assign_simple.find("="));
			
			if (right.find("global_") != std::string::npos){
				//es, lo tengo que insertar como lectura...
				vector<string> vtype = dbcommand("select type from uppaal_variables where name =\""+ right.substr(0,right.find(" ")) +"\";");

				//string type = *(vtype.begin());
				vector<string>::iterator iter = vtype.begin();
				string type = vtype.at(0);
				string s =cmd_option_str("seedfn").substr(2,3);
				const char * chr = s.c_str();
				int size=0;
				if(chr[1]>47 && chr[1]<58){
					s=cmd_option_str("seedfn").substr(2,3);
					size=atoi(s.c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(4,size), right.substr(7,right.substr(7).find(" ")), type, "Read");
				}else{
					s=cmd_option_str("seedfn").substr(2,2);
					size=atoi(s.c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(3,size), right.substr(7,right.substr(7).find(" ")), type, "Read");
				}
				
			}
			if (left.find("global_") != std::string::npos){
				//es, lo tengo que insertar como estritura...
				vector<string> vtype = dbcommand("select type from uppaal_variables where name = \""+ left +"\";");
				string type = *(vtype.begin());
				string s =cmd_option_str("seedfn").substr(2,3);
				const char * chr = s.c_str();
				int size=0;
				if(chr[1]>47 && chr[1]<58){
					size=atoi(cmd_option_str("seedfn").substr(2,3).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(4,size), left.substr(7), type, "Write");
				}else{
					size=atoi(cmd_option_str("seedfn").substr(2,2).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(3,size), left.substr(7), type, "Write");
				}
				
			}	
		}	
	}

}

void inserta_semaforos(){

	vector<string> sem = dbcommand("select distinct semaphore from uppaal;");
	for( vector<string>::iterator it = sem.begin(); it != sem.end(); it++ ){
		string semaphore = *it;
		if (semaphore.find("global_") != std::string::npos){
			vector<string> vnum = dbcommand("select COUNT(*) from uppaal where semaphore = \""+ semaphore +"\" and lockunlock= \"lock\";");
			string num = *(vnum.begin());
			int value= atoi(num.c_str());
			if(value>0){
				string s =cmd_option_str("seedfn").substr(2,3);
				const char * chr = s.c_str();
				int size=0;
				if(chr[1]>47 && chr[1]<58){
					size=atoi(cmd_option_str("seedfn").substr(2,3).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(4,size), semaphore.substr(7,semaphore.size()-8), "Mutex", "MutexLock");
				}else{
					size=atoi(cmd_option_str("seedfn").substr(2,2).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(3,size), semaphore.substr(7,semaphore.size()-8), "Mutex", "MutexLock");
				}
				
			}

			vnum = dbcommand("select COUNT(*) from uppaal where semaphore = \""+ semaphore +"\" and lockunlock= \"unlock\";");
			num = *(vnum.begin());
			value= atoi(num.c_str());
			if(value>0){
				string s =cmd_option_str("seedfn").substr(2,3);
				const char * chr = s.c_str();
				int size=0;
				if(chr[1]>47 && chr[1]<58){
					size=atoi(cmd_option_str("seedfn").substr(2,3).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(4,size), semaphore.substr(7,semaphore.size()-8), "Mutex", "MutexUnlock");
				}else{
					size=atoi(cmd_option_str("seedfn").substr(2,2).c_str());
					insert_uppaal_row(cmd_option_str("seedfn").substr(3,size), semaphore.substr(7,semaphore.size()-8), "Mutex", "MutexUnlock");
				}
				
			}	
		}
	}
}

void fill_table_uppaal(){
	inserta_asignamientos();
	inserta_semaforos();
}

void compare_tables(){
	string s =cmd_option_str("seedfn").substr(2,3);
	const char * chr = s.c_str();
	int size=0;
	string seed;
	if(chr[1]>47 && chr[1]<58){
		size=atoi(cmd_option_str("seedfn").substr(2,3).c_str());
		seed=cmd_option_str("seedfn").substr(4,size);
		
	}else{
		size=atoi(cmd_option_str("seedfn").substr(2,2).c_str());
		seed=cmd_option_str("seedfn").substr(3,size);
	}
	//int err=0;
	//COMPARO LA DE UPPAAL CON el XML	
	vector<string> vnumUppaal = dbcommand("SELECT COUNT(*) FROM  check_uppaal;");
	string numUppaal = *(vnumUppaal.begin());
	int valueUppaal= atoi(numUppaal.c_str());
	int i=0;
	for(i=0;i<valueUppaal;i++){
		stringstream s;
		s << i;
		vector<string> thread = dbcommand("SELECT nameThread FROM check_uppaal LIMIT "+s.str()+",1;");
		vector<string> var = dbcommand("SELECT nameVar FROM check_uppaal LIMIT "+s.str()+",1;");
		vector<string> type = dbcommand("SELECT type FROM check_uppaal LIMIT "+s.str()+",1;");
		vector<string> action = dbcommand("SELECT action FROM check_uppaal LIMIT "+s.str()+",1;");
		
		vector<string> comp = dbcommand("SELECT COUNT(*) FROM check_xml WHERE nameThread = \""+thread.at(0)+"\" AND nameVar=\""+var.at(0)+"\" AND action =\""+action.at(0)+"\";");
		int valcompare= atoi(comp.at(0).c_str());
		if(valcompare == 0){
			printf("Values not found in xmlfile nameThread= %s nameVar=%s type=%s action=%s \n",thread.at(0).c_str(), var.at(0).c_str(),type.at(0).c_str(), action.at(0).c_str());
			//err++;
		}
	}

	//COMPARO EL XML CON UPPAAL
	vector<string> vnumXml = dbcommand("SELECT COUNT(*) FROM  check_xml where nameThread=\""+seed+"\";");
	string numXml = *(vnumXml.begin());
	int valueXml= atoi(numXml.c_str());
	i=0;
	for(i=0;i<valueXml;i++){
		stringstream s;
		s << i;
		//vector<string> thread = dbcommand("SELECT nameThread FROM check_xml WHERE nameThread=\""+seed+"\" AND ROWNUM = "+i+";");
		vector<string> var = dbcommand("SELECT nameVar FROM check_xml WHERE nameThread=\""+seed+"\" LIMIT "+s.str()+",1;");
		vector<string> type = dbcommand("SELECT type FROM check_xml WHERE nameThread=\""+seed+"\" LIMIT "+s.str()+",1;");
		vector<string> action = dbcommand("SELECT action FROM check_xml WHERE nameThread=\""+seed+"\" LIMIT "+s.str()+",1;");
		
		vector<string> comp = dbcommand("SELECT COUNT(*) FROM check_uppaal WHERE nameThread = \""+seed+"\" AND nameVar=\""+var.at(0)+"\" AND action =\""+action.at(0)+"\";");
		int valcompare= atoi(comp.at(0).c_str());
		if(valcompare == 0){
			printf("Values not found in uppaal nameThread= %s nameVar= %s type= %s action= %s \n",seed.c_str(), var.at(0).c_str(),type.at(0).c_str(), action.at(0).c_str());
			//err++;
		}
	}

	/*if(err=0){
		printf("CHECK ERRORS CORRECT\n");
	}else{
		printf("CHECK ERRORS : DETECTED ERRORS\n");
	}*/
}

void compare_xml(){
	//printf("relleno tablas xml\n");
	fill_table_xml();
	//printf("relleno tablas uppaal\n");
	fill_table_uppaal();
	//printf("comparo\n");
	compare_tables();

}


