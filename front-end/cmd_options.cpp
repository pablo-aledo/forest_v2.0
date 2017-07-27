/*
 * =====================================================================================
 * /
 * |     Filename:  cmd_options.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 03:06:26 PM
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

#include "cmd_options.h"

#define SIZE_STR 1024

string project_path;
string current_path;

std::map<std::string, std::string> options; // Options in XML File or command line


void set_option( string key, string value ){
	options[key] = value;
}

void load_cmd_options(int argc, const char** argv ){


	if( argc >= 2 && argv[1][0] != '-' ){
		argc = argc - 1;
		argv = argv + 1;
	}
	
	vector<string> tokens; // Words in command line
	
	for( int n = 1; n < argc; n++ ){
		char* token_str; // element in command line
		if( argv[n][0] == '-' && argv[n][1] != '-' )
			token_str = (char*)argv[n];
		else if( argv[n][0] == '-' && argv[n][1] == '-' )
			token_str = (char*)argv[n]+1;
		else
			token_str = (char*)argv[n];
		
		string token( token_str ); // Each word in command line
		tokens.push_back( token );	
	}
	
	
	for( unsigned int n = 0; n < tokens.size(); ){
		if( tokens[n][0] == '-' && ( (int)n+2 == argc || tokens[n+1][0] == '-' ) ){
			options[ tokens[n].substr(1) ] = "true";
			n++;
			continue;
		}
		
		if( tokens[n][0] == '-' && tokens[n+1][0] != '-' ){
			options[ tokens[n].substr(1) ] = tokens[n+1];
			n++;n++;
			continue;
		}
	}
	
	
	
	
}

int cmd_option_int(string option){
	return atoi( options[option].c_str() );
}

string cmd_option_str(string option){
	if(options[option] == "" ) return "";
	vector<string> tokens = tokenize(options[option].c_str(),"@" );
	string ret = tokens[tokens.size()-1];
	return ret;
}

bool cmd_option_bool(string option){

	string opt;

	if( options[option].find("@") != string::npos ){
		vector<string> tokens = tokenize(options[option], "@");
		opt = tokens[tokens.size()-1];
	} else {
		opt = options[option];
	}
	return opt == "true" || opt == "True" ;
}

float cmd_option_float(string option){
	return atof( options[option].c_str() );
}

vector<string> cmd_option_string_vector(string option){
	return tokenize( options[option], "@" );
}

vector<int> cmd_option_int_vector(string option){
	vector<string> vector_str = tokenize( options[option], "@");
	vector<int> vector_int;

	for ( unsigned int i = 0; i < vector_str.size(); i++) {
		vector_int.push_back( atoi( vector_str[i].c_str() ) );
	}
	return vector_int;
}

vector<float> cmd_option_float_vector(string option){
	vector<string> vector_str = tokenize( options[option], "@");
	vector<float> vector_float;

	for ( unsigned int i = 0; i < vector_str.size(); i++) {
		vector_float.push_back( atof( vector_str[i].c_str() ) );
	}
	return vector_float;
}

void load_file_options(string file){

	ifstream input(file.c_str());
	string line;
	
	if( !getline( input, line ) )
		return;
	


	TiXmlDocument doc(file.c_str()); // XML Document
	doc.LoadFile();
	
	std::string m_name; // Name
	
	TiXmlHandle hDoc(&doc); // XML handler
	TiXmlElement* pElem; // Each element
	TiXmlHandle hRoot(0); // XML Root
	
	pElem=hDoc.FirstChildElement("options").Element();
	m_name=pElem->Value();
	
	hRoot=TiXmlHandle(pElem);

	pElem=hRoot.FirstChild().Element();
	for( ; pElem; pElem=pElem->NextSiblingElement()){


		bool found = false;
		for( map<string, string>::iterator it = options.begin(); it != options.end(); it++){


			if( it->first == pElem->Attribute("key") ){
				found = 1;
				break;
			} else {
				found = 0;
			}
		}


		if(found){
			options[pElem->Attribute("key")] += ( string( "@" ) + pElem->Attribute("value") );
		} else {
			options[pElem->Attribute("key")] = pElem->Attribute("value");
		}


	}
	
}

void load_default_options(){
	options["verbose"] = "false";
	options["base_path"] = "/media/disk/release";
	options["llvm_path"] = "/llvm-2.9";
	options["output_file"] = "final";
	options["subst_names"] = "true";
	options["driver"] = "real_integer";
	//options["link_bc"] = "true";
	options["propagate_constants"] = "true";
	options["max_pointer_deref_combs"] = "500";
	options["max_partitions_for_ineq"] = "5";
	//options["solver"] = "bitvector";
	options["check_outofbounds"] = "true";
	options["solver"] = "real_integer";
	//options["solver"] = "linear";
	//options["solver"] = "mixed_int";
	//options["solver"] = "linear_bblast";
	//options["solver"] = "polynomic";
	//options["solver"] = "mixed_bblast";
	//options["solver"] = "interpolants";
	//options["solver"] = "all_solvers";
	//options["compare_klee"] = "true";
	//options["get_result"] = "true";
	options["sequential_problems"] = "true";
	options["bigsize"] = "5";
	options["max_time_min"] = "5";
	options["witness"] = "witness.graphml";
	options["check_witness"] = "false";
	options["uppaal_scale"] = "1";
	options["stack_start"] = "10000";
	options["stack_size"] = "10";
	options["stack_step"] = "10";

	if(string(getenv("FOREST_HOME")) != "")
		set_option("base_path", string(getenv("FOREST_HOME")));
	if(string(getenv("LLVM_HOME")) != "")
		set_option("llvm_path", string(getenv("LLVM_HOME")));
	if(string(getenv("CPACHECKER_HOME")) != "")
		set_option("cpachecker_path", string(getenv("CPACHECKER_HOME")));
	if(string(getenv("CSEQ_HOME")) != "")
		set_option("cseq_path", string(getenv("CSEQ_HOME")));

}

void load_file_options(){
	load_file_options(string("config.xml"));
}

void cmd_option_set(string key, string value ){

	options[key] = value;


}


void options_to_file(){

	FILE* file = fopen(tmp_file("options").c_str(), "w");

	for( map<string,string>::iterator it = options.begin(); it != options.end(); it++ ){
		fprintf(file, "%s %s\n", it->first.c_str(), it->second.c_str());
	}
	fclose(file);
}

void set_current_path(){
	char current_path_c[SIZE_STR];
	strcpy(current_path_c, getenv("PWD"));
	current_path = string(current_path_c);

	cmd_option_bool("verbose") && printf("current_path %s\n", current_path.c_str());
}

void set_project_path( string file ){

	vector<string> tokens = tokenize(file, "/");

	string path_aux = "/";

	for ( unsigned int i = 0; i < tokens.size() - 1; i++) {
		path_aux += tokens[i] + "/";
	}

	project_path = path_aux;
	if(project_path == ""){
		project_path = current_path;
	} else {
		project_path = project_path.substr(0, project_path.length()-1);
		myReplace(project_path, "/./", current_path + "/");
	}

	cmd_option_bool("verbose") && printf("project_path %s\n", project_path.c_str());
	

}


string get_project_path(){
	return project_path;
}

string get_current_path(){
	return current_path;
}


vector<string> file_as_vector_without_includes(string filename){

	ifstream input(filename.c_str());
	string line;
	vector<string> lines;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}

	int firstline = 0;
	for ( unsigned int i = 0; i < lines.size();) {
		//printf("i %d\n", i);
		if(lines[i].find("extern") != string::npos && \
		   lines[i].find("VERIFIER") == string::npos ){
			while( i < lines.size()-1 && lines[i] != "" ){
				//printf("I %d\n", i);
				i++;
				firstline = i;
			}
		}
		i++;
	}


	for ( unsigned int i = 0; i < firstline; i++) {
		lines.erase(lines.begin());
	}

	return lines;
	
}

bool calls_to_malloc(string filename){

	vector<string> file = file_as_vector_without_includes(filename);

	for( vector<string>::iterator it = file.begin(); it != file.end(); it++ ){
		if(it->find("malloc") != string::npos) return true;
		if(it->find("free") != string::npos) return true;
		if(it->find("alloca") != string::npos) return true;
	}
	
	return false;
}

bool is_concurrent(string filename){

	vector<string> file = file_as_vector_without_includes(filename);

	for( vector<string>::iterator it = file.begin(); it != file.end(); it++ ){
		if(it->find("pthread") != string::npos) return true;
	}
	
	return false;
}

bool is_recursive(string filename){
	string llvm_path = cmd_option_str("llvm_path");
	stringstream command;
	command << "llvm-gcc " << filename << " -c --emit-llvm -o " << tmp_file("check_recursive") << ";";
	command << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestFeatures.so -isrecursive < " << tmp_file("check_recursive") << " > /dev/null";
	systm(command.str().c_str());

	int ret;
	FILE* file = fopen(tmp_file("recursive").c_str(), "r");
	fscanf(file, "%d", &ret);
	fclose(file);

	if(ret){
		//printf("Program is recursive\n");
	} else {
		//printf("Program is not recursive\n");
	}

	return ret;

}


void guess_options(string filename){
	set_option("check_outofbounds", calls_to_malloc(filename)?string("true"):string("false"));
	set_option("recursive",         is_recursive(filename)?string("true"):string("false"));
	set_option("sequentialize",     is_concurrent(filename)?string("true"):string("false"));
}

void expand_options(){

	disable_options();

	if(cmd_option_bool("guess_options") || cmd_option_bool("svcomp"))
		guess_options(prj_file(cmd_option_str("file")));

	if(cmd_option_bool("svcomp") || cmd_option_bool("goanna_fpr") ){
		set_option("drive_frontend", "true");
		set_option("use_db_for_fi", "true");
		set_option("rm_z3_queries", "true");
		//set_option("target_node", "VERIFIERassert_ERROR");
		set_option("target_node", "error_ERROR");
		set_option("max_time_min", "14");
		set_option("sym_argvs", "1 2 3");
		set_option("llvm_path", string(getenv("LLVM_HOME")));
		set_option("base_path", string(getenv("FOREST_HOME")));
		set_option("cpachecker_path", string(getenv("CPACHECKER_HOME")));
		set_option("rm_include", "true");
		set_option("c_standard", "C");
		set_option("check_without_instrumentation", "true");

		if(cmd_option_bool("recursive") || cmd_option_bool("sequentialize"))
			set_option("force_run", "true");
		
		set_option("workaround_subst", "true");

		if(cmd_option_bool("recursive")){
			set_option("heuristic_recursive_depth", "5");
			set_option("max_depth", "125");
			set_option("max_heuristic_paths", "20");
			set_option("solver", "real_integer");
		} else {
			set_option("heuristic_recursive_depth", "5");
			set_option("max_depth", "105");
			set_option("max_heuristic_paths", "20");
		}
	}

	if(cmd_option_bool("goanna_fpr")) set_option("svcomp_silent", "true");
	if(cmd_option_bool("goanna_fpr")) set_option("complete", "true");
}

