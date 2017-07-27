/*
 * =====================================================================================
 * /
 * |     Filename:  models.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 06:15:33 PM
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

#include "models.h"

vector<string> get_model_paths(){

	stringstream cmd;
	cmd << "cd " << tmp_dir() << ";";
	cmd << "echo 'select path from models;' | sqlite3 database.db";
	cmd << " > model_paths";
	system(cmd.str().c_str());

	vector<string> lines;
	string line;

	ifstream input(tmp_file("model_paths").c_str());
	
	while( getline( input, line ) ) {
		if(line == "")
			lines.push_back("true");
		else
			lines.push_back(line);
	}
	
	return lines;
	
}

vector<string> get_model_assigns(){

	stringstream cmd;
	cmd << "cd " << tmp_dir() << ";";
	cmd << "echo 'select content from models;' | sqlite3 database.db";
	cmd << " > model_assigns";
	system(cmd.str().c_str());

	vector<string> lines;

	ifstream input(tmp_file("/model_assigns").c_str());
	string line;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}
	
	

	return lines;
	
}

vector<string> get_model_names(){

	stringstream cmd;
	cmd << "cd " << tmp_dir() << ";";
	cmd << "echo 'select variable from models;' | sqlite3 database.db";
	cmd << " > model_variables";
	system(cmd.str().c_str());

	ifstream input(tmp_file("model_variables").c_str());
	string line;
	vector<string> lines;
	
	while( getline( input, line ) ) {
		lines.push_back(line);
	}

	return lines;
	
}

string z3_type(string type){
	if(cmd_option_str("solver") == "real_integer"){
		if(type == "Pointer")
			return "Int";
		if(type == "FloatTyID")
			return "Real";
		if(type == "IntegerTyID32")
			return "Int";
		if(type == "IntegerTyID8")
			return "Int";
	} else {
		if(type == "Pointer")
			return "(_ BitVec 32)";
		if(type == "FloatTyID")
			return "(_ BitVec 32)";
		if(type == "IntegerTyID32")
			return "(_ BitVec 32)";
		if(type == "IntegerTyID8")
			return "(_ BitVec 8)";
	}

	return type;
}

set<string> get_model_freevars(){

	stringstream cmd;
	cmd << "cd " << tmp_dir() << ";";
	//cmd << "echo 'select distinct position,type from variables;' | sqlite3 database.db";
	cmd << "echo 'select distinct position,type from free_variables;' | sqlite3 database.db";
	cmd << " > model_free";
	system(cmd.str().c_str());

	FILE *file = fopen( tmp_file("model_free").c_str() , "r" );
	static char line [ 50000 ]; /* or other suitable maximum line size */
	vector<string> lines;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		lines.push_back(string(line));
	}
	fclose ( file );

	set<string> free_vars;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		vector<string> tokens = tokenize(*it, "|");
		free_vars.insert(tokens[0] + ":" + z3_type(tokens[1]));
		
	}
	

	return free_vars;

}

set<string> get_model_outputs(){

	stringstream cmd;
	cmd << "cd " << tmp_dir() << ";";
	cmd << "echo 'select variable from models;' | sqlite3 database.db";
	cmd << " > model_outputs";
	system(cmd.str().c_str());

	FILE *file = fopen ( tmp_file("model_outputs").c_str() , "r" );
	static char line [ 50000 ]; /* or other suitable maximum line size */
	vector<string> lines;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		lines.push_back(string(line));
	}
	fclose ( file );

	set<string> outputs;

	for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
		outputs.insert(*it);
		
	}
	

	return outputs;

}

void and_paths(vector<string>& paths){
	
	for ( unsigned int i = 0; i < paths.size(); i++) {
		vector<string> paths_v = tokenize(paths[i], ",");
		string path;

		path = "(and ";
		for ( unsigned int k = 0; k < paths_v.size(); k++) {
			path += ( paths_v[k] + " " );
		}
		path += ")";

		paths[i] = path;
	}
	
}

void get_model(){

	vector<string> paths   = get_model_paths();
	vector<string> assigns = get_model_assigns();
	vector<string> names   = get_model_names();
	set<string>    free_v  = get_model_freevars();
	set<string>    outputs = get_model_outputs();

	and_paths(paths);

	//printf("paths and models %lu %lu\n", paths.size(), assigns.size());

	assert(paths.size() == assigns.size());
	assert(paths.size() == names.size());

	stringstream model;
	model << "content:(assert (or ";

	for ( unsigned int i = 0; i < paths.size(); i++) {
		string path = paths[i];
		string assign = assigns[i];
		string name = names[i];

		model << "(and " << "(= " << name << " " << assign << ") " << path << ") ";
	}
	model << "))";

	printf("solver:%s\n", cmd_option_str("solver").c_str());

	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		printf("input:%s\n", it->c_str());
	}

	for( set<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){
		printf("output:%s\n", it->c_str());
	}
	

	printf("%s\n", model.str().c_str());


	
}

set<string> to_set(vector<string> input){
	set<string> ret;
	for( vector<string>::iterator it = input.begin(); it != input.end(); it++ ){
		ret.insert(*it);
	}
	return ret;
}

string filter(string path, vector<string> names, vector<string> assigns, vector<string> paths){
	string ret;

	assert(names.size() == assigns.size());
	assert(assigns.size() == paths.size());

	for ( unsigned int i = 0; i < paths.size(); i++) {
		if(paths[i] == path){
			ret += "(= " + names[i] + " " + assigns[i] + ") ";
		}
	}


	return ret;
}

void get_model_modelfinder(){

	vector<string> paths   = get_model_paths();
	vector<string> assigns = get_model_assigns();
	vector<string> names   = get_model_names();
	set<string>    free_v  = get_model_freevars();
	set<string>    outputs = get_model_outputs();

	and_paths(paths);

	//printf("paths and models %lu %lu\n", paths.size(), assigns.size());

	assert(paths.size() == assigns.size());
	assert(paths.size() == names.size());

	stringstream model;
	model << "content:(= implementation (or ";

	set<string> paths_s = to_set(paths);

	for( set<string>::iterator it = paths_s.begin(); it != paths_s.end(); it++ ){
		string path = *it;
		string assigns_s = filter(path, names, assigns, paths);
		model << "(and " << assigns_s << path << ") ";
	}
	

	model << "))";

	printf("solver:%s\n", cmd_option_str("solver").c_str());

	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		printf("input:%s\n", it->c_str());
	}

	for( set<string>::iterator it = outputs.begin(); it != outputs.end(); it++ ){
		printf("output:%s:(_ BitVec 8)\n", it->c_str());
	}
	printf("output:implementation:Bool\n");
	

	printf("%s\n", model.str().c_str());


	
}
void pass_1(vector<Node>& nodes){

	map<string, int> map_contents;
	set<string> set_contents;
	int num_nodes = nodes.size();

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].assign != "" && set_contents.find(nodes[i].assign) == set_contents.end() ){
			map_contents[ nodes[i].assign ] = num_nodes;
			set_contents.insert(nodes[i].assign);
			num_nodes++;
		}
	}

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].assign != ""){
			vector<ParentStruct> parents = get_parents(nodes, i);
			int node_dest = map_contents[ nodes[i].assign ];

			for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					nodes[it->node].node_pos = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					nodes[it->node].node_neg = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					nodes[it->node].node_pos = node_dest;
					nodes[it->node].node_neg = node_dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				}
			}
		}
	}

	for( set<string>::iterator it = set_contents.begin(); it != set_contents.end(); it++ ){
		Node node = { "", -1, -1, *it};
		nodes.push_back(node);
	}
	

}

void pass_2(vector<Node>& nodes){
	//return;
	for ( unsigned int i = 0; i < nodes.size(); i++) {
	//unsigned int i = 19;{
		for ( unsigned int k = 0; k < nodes.size(); k++) {
		//unsigned int k = 11; {
			if(nodes[i].node_pos == nodes[k].node_pos && nodes[i].node_neg == nodes[k].node_neg){

				if(nodes[i].node_pos == -1 && nodes[i].node_neg == -1 ) continue;
				if(nodes[k].node_pos == -1 && nodes[k].node_neg == -1 ) continue;
				if( i == k ) continue;

				vector<ParentStruct> parents = get_parents(nodes, k);

				for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
					if(it->branch == "pos"){
						nodes[it->node].node_pos = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					} else if(it->branch == "neg"){
						nodes[it->node].node_neg = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					} else if(it->branch == "both"){
						nodes[it->node].node_pos = i;
						nodes[k].assign = ""; nodes[k].node_pos = nodes[k].node_neg = -1;
					}
				}
				
			}
		}
	}

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( (nodes[i].node_pos == -1 && nodes[i].node_neg == -1) && nodes[i].cond_pos != ""){
			vector<ParentStruct> parents = get_parents(nodes, i);
			for ( unsigned int k = 0; k < parents.size(); k++) {
				int n = parents[k].node;
				nodes[n].assign = ""; nodes[n].node_pos = nodes[n].node_neg = -1;
			}
		}
	}
	
}

void pass_3(vector<Node>& nodes){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( nodes[i].node_pos == nodes[i].node_neg ){

			if(nodes[i].node_pos == -1) continue;

			vector<ParentStruct> parents = get_parents(nodes,i);
			int dest = nodes[i].node_pos;

			for( vector<ParentStruct>::iterator it = parents.begin(); it != parents.end(); it++ ){
				if(it->branch == "pos"){
					nodes[it->node].node_pos = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "neg"){
					nodes[it->node].node_neg = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				} else if(it->branch == "both"){
					nodes[it->node].node_pos = dest;
					nodes[i].assign = ""; nodes[i].node_pos = nodes[i].node_neg = -1;
				}
			}
		}
	}
}

vector<ParentStruct> get_parents(vector<Node> nodes, int n){

	vector<ParentStruct> ret;
	ParentStruct ps;

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].node_pos == n && nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "both";
			ret.push_back(ps);
		} else if(nodes[i].node_pos == n){
			ps.node = i;
			ps.branch = "pos";
			ret.push_back(ps);
		} else if(nodes[i].node_neg == n){
			ps.node = i;
			ps.branch = "neg";
			ret.push_back(ps);
		}
	}
	return ret;
}

void rm_invalid_nodes(vector<Node>& nodes){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if( nodes[i].node_pos == -1 && nodes[i].node_neg == -1 && nodes[i].assign == "" ){
			nodes.erase(nodes.begin() + i);i--;
		}
	}
}

void robdd(vector<Node>& nodes){
	pass_1(nodes);
	pass_2(nodes);
	pass_3(nodes);
	//rm_invalid_nodes(nodes);
}

void get_model_fn(){

	vector<string> paths   = get_model_paths();
	vector<string> assigns = get_model_assigns();
	vector<string> names   = get_model_names();
	set<string>    free_v  = get_model_freevars();
	set<string>    outputs = get_model_outputs();

	assert(paths.size() == assigns.size());
	assert(paths.size() == names.size());

	stringstream model;
	model << "function:(define-fun gcd ( ";
	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		model << "(" << *it << " Int) ";
	}
	model << ") Int ";
	

	vector<PathAndAssign> path_and_assigns;

	//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(= main_register_b 0)"      ,  ","); pa.assign = "1"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(a),(not (b))"        ,  ","); pa.assign = "2"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(not (a)),(b)"        ,  ","); pa.assign = "3"; path_and_assigns.push_back(pa); }
	//{ PathAndAssign pa; pa.path = tokenize("(not (a)),(not (b))"  ,  ","); pa.assign = "4"; path_and_assigns.push_back(pa); }
	
//{ PathAndAssign pa; pa.path = tokenize("(not (= main_register_a 0)),(not (= main_register_b 0))", ","); pa.assign = "0"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(not (= main_register_a 0)),(= main_register_b 0)", ","); pa.assign = "1"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(not (= main_register_b 0))", ","); pa.assign = "1"; path_and_assigns.push_back(pa);}
//{ PathAndAssign pa; pa.path = tokenize("(= main_register_a 0),(= main_register_b 0)", ","); pa.assign = "2"; path_and_assigns.push_back(pa);}
	
	
	
	for ( unsigned int i = 0; i < paths.size(); i++) {
		PathAndAssign pa;
		pa.path = tokenize(paths[i], ",");
		pa.assign = assigns[i];
		path_and_assigns.push_back(pa); 
	}

	normalize(path_and_assigns);

	//for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ ){
		//PathAndAssign path_and_assign = *it;
		//print_path_assign(path_and_assign);
	//}

	

	set<string> variables_set = get_set_variables(path_and_assigns);
	vector<string> variables_vec = vector<string>(variables_set.begin(), variables_set.end());

	//if(cmd_option_int("bdd_permutation"))
		//permute(variables_vec);

	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x3 0),(= main_register_x5 0),(= main_register_x7 0),(= main_register_x2 0),(= main_register_x4 0),(= main_register_x6 0),(= main_register_x8 0)", ",");
	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x2 0),(= main_register_x3 0),(= main_register_x4 0),(= main_register_x5 0),(= main_register_x6 0),(= main_register_x7 0),(= main_register_x8 0)", ",");
	//variables_vec = tokenize("(= main_register_x1 0),(= main_register_x2 0),(= main_register_x3 0)", ",");

	//for( vector<string>::iterator it = variables_vec.begin(); it != variables_vec.end(); it++ ){
		//printf("variable %s\n", it->c_str());
	//}
	
	
	vector<Node> nodes;
	make_tree(nodes, path_and_assigns, variables_vec);
	robdd(nodes);
	if(cmd_option_bool("show_bdd")) show_bdd(nodes);

	model << get_ite_expr(nodes);
	
	//exit(0);

	model << ")";


	for( set<string>::iterator it = free_v.begin(); it != free_v.end(); it++ ){
		printf("input:%s\n", it->c_str());
	}

	printf("%s\n", model.str().c_str());

}

void normalize(PathAndAssign& path_and_assign){

	Path path = path_and_assign.path;

	for ( unsigned int i = 0; i < path.size(); i++) {
		string cond = path[i];

		while(cond.substr(0,10) == "(not (not "){
			string right = cond.substr(10);
			cond = right.substr(0,right.length()-2);
		}

		path[i] = cond;
	}
	
	path_and_assign.path = path;
}

void normalize(vector<PathAndAssign>& path_and_assigns){

	for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ )
		normalize(*it);
	
}

string get_ite_expr(vector<Node> nodes, int n){
	Node node = nodes[n];
	if(node.node_pos == -1 || node.node_neg == -1)
		return (node.assign == "")?"0":node.assign;

	return string("(ite ") + " " + node.cond_pos + " " + get_ite_expr(nodes, node.node_pos) + " " + get_ite_expr(nodes, node.node_neg) + ")";
}

set<string> get_set_variables(vector<PathAndAssign> path_and_assigns){

	set<string> ret;
	for( vector<PathAndAssign>::iterator it = path_and_assigns.begin(); it != path_and_assigns.end(); it++ ){
		Path path = it->path;
		for( vector<string>::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			string cond = *it2;
			if( cond.substr(0,5) == "(not ")
				ret.insert(negation(*it2));
			else
				ret.insert(*it2);
		}
	}

	return ret;
	
}

void make_tree(vector<Node>& nodes, vector<PathAndAssign> paths_and_assign, vector<string> cond_ordering , int depth ){

	if( paths_and_assign.size() == 1 ){
		add_path(nodes, paths_and_assign[0]);
		return;
	}

	for( vector<string>::iterator it = cond_ordering.begin(); it != cond_ordering.end(); it++ ){
		//printf("variable %s\n", it->c_str());
		if(is_complete(*it, paths_and_assign)){
			//printf("is_complete\n");
			vector<PathAndAssign> paths_pos;
			vector<PathAndAssign> paths_neg;
			part_paths(*it,paths_and_assign, paths_pos, paths_neg);

			get_to_front(paths_pos, *it, depth);
			get_to_front(paths_neg, *it, depth);

			assert(paths_pos.size() + paths_neg.size() == paths_and_assign.size());

			make_tree(nodes, paths_pos, remove(cond_ordering, *it) , depth + 1);
			make_tree(nodes, paths_neg, remove(cond_ordering, *it) , depth + 1);
		}
	}
	
}

void show_bdd(vector<Node> nodes, string title ){

		FILE* file = fopen(tmp_file("digraph").c_str(), "w");
		fprintf(file, "digraph G{\n");
		for ( unsigned int i = 0; i < nodes.size(); i++) {
			Node n = nodes[i];

			if(nodes[i].node_pos != -1 ) fprintf(file, "%d -> %d [color=\"green\"]\n", i, nodes[i].node_pos );
			if(nodes[i].node_neg != -1 ) fprintf(file, "%d -> %d [color=\"red\"]\n",   i, nodes[i].node_neg );
			//if(nodes[i].node_pos != -1 ) fprintf(file, "%d -> %d [color=\"red\"]\n", i, nodes[i].node_pos );
			//if(nodes[i].node_neg != -1 ) fprintf(file, "%d -> %d [color=\"green\"]\n",   i, nodes[i].node_neg );

		}

		fprintf(file, "legend_1 [shape=none, margin=0, label=<");
		fprintf(file, "<table border='0' cellborder='0'>");

		if(title != ""){
			fprintf(file, "<tr><td>");
			fprintf(file, "%s", title.c_str());
			fprintf(file, "</td></tr>\n");
		}


		for ( unsigned int i = 0; i < nodes.size(); i++) {


			if(nodes[i].node_pos == -1 && nodes[i].node_neg == -1 && nodes[i].assign == "")
				continue;

			stringstream row;
			string cond_pos = nodes[i].cond_pos; if(cond_pos == "") cond_pos = "-"; if(cond_pos.length() > 20) cond_pos = cond_pos.substr(0,20) + "...";
			string assign   = nodes[i].assign;   if(assign   == "") assign   = "-"; if(assign.length()   > 20) assign   =   assign.substr(0,20)  + "...";
			int node_pos = nodes[i].node_pos;
			int node_neg = nodes[i].node_neg;
			row << "<tr>"; 

			row << "<td align='left'>";
			row << i;
			row << "</td>";

			row << "<td align='left'>";
			row << "<font color='green'>" << cond_pos << "</font>";
			row << "</td>";

			row << "<td align='left'>";
			row << "<font color='blue'>" << assign << "</font>";
			row << "</td>";

			row << "</tr>"; 

			fprintf(file, "%s\n", row.str().c_str());

		}
		//fprintf(file, "<tr><td align='left'><font color='red'> hola </font></td></tr>");
		//fprintf(file, "<tr><td align='left'> adiosssss </td></tr>");
		fprintf(file, "</table>");
		fprintf(file, ">];");



		fprintf(file, "}\n");
		fclose(file);
		system(("cat " + tmp_file("digraph") + " | dot -Tpng > " + tmp_file("digraph.png") + " 2>/dev/null").c_str());
		system(("eog " + tmp_file("digraph") + " 2>/dev/null").c_str());
}

string negation(string cond){
	if(cond.substr(0,4) == "(not"){
		string right = cond.substr(5);
		string center = right.substr(0, right.length()-1);
		return center;
	} else {
		return "(not " + cond + ")";
	}
}

void add_path(vector<Node>& nodes, PathAndAssign path_and_assign, int node_root ){


	Path path = path_and_assign.path;
	string cond = path.size()? path[0]:"";
	string assign = path_and_assign.assign;


	if(!nodes.size()){
		Node node = {positive_cond(cond), -1, -1, ""};
		insert_node(nodes, node);
		add_path(nodes, path_and_assign, node_root);
	}

	bool follow_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos != -1);
	bool follow_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg != -1);
	bool create_pos  = (nodes[node_root].cond_pos == cond && nodes[node_root].node_pos == -1);
	bool create_neg  = (nodes[node_root].cond_pos == negation(cond) && nodes[node_root].node_neg == -1);
	bool is_terminal = (path.size() == 1);

	//printf("-----------\n");
	//printf("add_path\n");
	//print_path_assign(path_and_assign);
	//printf("node_root %d\n", node_root);
	//printf("cond %s\n", cond.c_str());
	//printf("follow_pos %d follow_neg %d create_pos %d create_neg %d is_terminal %d\n", follow_pos, follow_neg, create_pos, create_neg, is_terminal);

	//show_bdd(nodes);

	if(follow_pos && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		return;
	}

	if(follow_neg && !is_terminal){
		add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg);
		return;
	}

	if(create_pos){
		if(is_terminal){
			new_node_pos(nodes, node_root);
			Node node = { "", -1, -1, assign};
			insert_node(nodes, node);
		} else {
			new_node_pos(nodes, node_root);
			Node node = { positive_cond( path[1] ), -1, -1, ""};
			insert_node(nodes, node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_pos );
		}
	}

	if(create_neg){
		if(is_terminal){
			new_node_neg(nodes, node_root);
			Node node = { "", -1, -1, assign};
			insert_node(nodes, node);
		} else {
			new_node_neg(nodes, node_root);
			Node node = {positive_cond( path[1] ), -1, -1, ""};
			insert_node(nodes, node);
			add_path(nodes, tail(path_and_assign), nodes[node_root].node_neg );
		}
	}




}

bool is_complete(string variable, vector<PathAndAssign> table){

	for( vector<PathAndAssign>::iterator it = table.begin(); it != table.end(); it++ ){
		PathAndAssign path_and_assign = *it;
		Path path = path_and_assign.path;
		bool found = false;
		for( Path::iterator it2 = path.begin(); it2 != path.end(); it2++ ){
			if(*it2 == variable || negation(*it2) == variable)
				found = true;
		}
		if(!found) return false;
		
	}
	
	return true;
}

void part_paths(string cond, vector<PathAndAssign> input, vector<PathAndAssign>& output_pos, vector<PathAndAssign>& output_neg ){

	for( vector<PathAndAssign>::iterator it = input.begin(); it != input.end(); it++ ){
		Path path = it->path;
		if( contains_pos(path, cond) )
			output_pos.push_back(*it);
		else if( contains_neg(path, cond))
			output_neg.push_back(*it);
		else
			assert(0 && "Malformed BDD");
	}
	
	
}

PathAndAssign get_to_front(PathAndAssign path_and_assign, string cond_pos, int depth){

	//printf("get_to_front\n---");
	//print_path_assign(path_and_assign);
	//printf("cond_pos %s\n", cond_pos.c_str() );

	Path path = path_and_assign.path;
	string assign = path_and_assign.assign;

	Path path_without_cond;
	string cond;

	for( Path::iterator it = path.begin(); it != path.end(); it++ ){

		if( cond_pos == *it || cond_pos == negation(*it) ){
			cond = *it;
		} else {
			path_without_cond.push_back(*it);
		}
	}

	PathAndAssign path_and_assign_ret;
	path_and_assign_ret.path = put_nth(cond, path_without_cond, depth);
	path_and_assign_ret.assign = assign;

	//printf("\n+++");
	//print_path_assign(path_and_assign_ret);

	return path_and_assign_ret;
}

void get_to_front(vector<PathAndAssign>& path_and_assigns, string cond_pos, int depth){


	for ( unsigned int i = 0; i < path_and_assigns.size(); i++) {
		path_and_assigns[i] = get_to_front(path_and_assigns[i], cond_pos, depth);
	}
	
}

vector<string> remove(vector<string>input , string to_remove){
	vector<string> ret;
	for( vector<string>::iterator it = input.begin(); it != input.end(); it++ ){
		if(*it != to_remove)
			ret.push_back(*it);
	}
	return ret;
}

string positive_cond(string condition){
	if(condition.substr(0,5) == "(neg ") return negation(condition);
	return condition;
}

void insert_node(vector<Node>& nodes, Node node){
	//printf("insert_node %lu\n", nodes.size());
	nodes.push_back(node);
}

PathAndAssign tail(PathAndAssign path_and_assign){

	PathAndAssign ret = path_and_assign;
	Path::iterator it_begin = path_and_assign.path.begin() + 1;
	Path::iterator it_end   = path_and_assign.path.end();
	Path retpath = Path(it_begin, it_end);
	ret.path = retpath;

	return ret;
}

void new_node_pos(vector<Node>& nodes, int node_root){
	//printf("set node_pos %d %lu\n", node_root, nodes.size());
	nodes[node_root].node_pos = nodes.size();
}

void new_node_neg(vector<Node>& nodes, int node_root){
	//printf("set node_neg %d %lu\n", node_root, nodes.size());
	nodes[node_root].node_neg = nodes.size();
}

bool contains_pos(Path path, string cond){
	for( Path::iterator it = path.begin(); it != path.end(); it++ ){
		if( cond == *it )
			return true;
	}

	return false;
	
}

bool contains_neg(Path path, string cond){
	for( Path::iterator it = path.begin(); it != path.end(); it++ ){
		if( "(not " + cond + ")" == *it )
			return true;
	}

	return false;
	
}

Path put_nth(string cond, Path path, int depth){

	//printf("put_nth\n");
	//print_path(path);
	//printf("cond %s\n", cond.c_str());
	//printf("depth %d\n", depth);

	Path ret;

	int n = 0;
	for( vector<string>::iterator it = path.begin(); it != path.end(); it++,n++ ){
		if( n==depth )
			ret.push_back(cond);
		ret.push_back(*it);
	}

	if(depth == path.size())
		ret.push_back(cond);
	
	return ret;
}

//void permute(vector<string>& variables_vec){

	//for ( unsigned int i = 0; i < cmd_option_int("bdd_permutation"); i++) {
		//next_permutation(variables_vec.begin(), variables_vec.end());
	//}

//}

void print_path_assign(PathAndAssign pa){

	Path path = pa.path;
	string assign = pa.assign;
	for( vector<string>::iterator it = path.begin(); it != path.end(); it++ ){
		printf("%s ", it->c_str());
	}
	printf(": %s\n",assign.c_str());
	
}

void print_path(Path path){

	for( vector<string>::iterator it = path.begin(); it != path.end(); it++ ){
		printf("%s ", it->c_str());
	}
	printf("\n");
	
}

