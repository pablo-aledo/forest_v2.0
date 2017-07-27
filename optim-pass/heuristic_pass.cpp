/*
 * =====================================================================================
 * /
 * |     Filename:  heuristic_pass.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  01/29/2014 01:19:20 PM
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


#include "/media/disk/release/back-end/sqlite3.h"
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Instructions.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/ADT/APFloat.h"
#include <sstream>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <map>


#include <limits>
#include <set>
#include <map>
#include <queue>
#include <string>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
#include "GraphElements.h"
#include "Graph.h"
#include "DijkstraShortestPathAlg.h"
#include "YenTopKShortestPathsAlg.h"

#define mod_iterator(mod, fn) for( Module::iterator        fn = mod.begin(),  function_end    = mod.end();  fn != function_end;    ++fn )
#define glo_iterator(mod, gl) for( Module::global_iterator gl = mod.global_begin(), gl_end    = mod.global_end();  gl != gl_end;   ++gl )
#define fun_iterator(fun, bb) for( Function::iterator      bb = fun->begin(), block_end       = fun->end(); bb != block_end;       ++bb )
#define blk_iterator(blk, in) for( BasicBlock::iterator    in = blk->begin(), instruction_end = blk->end(); in != instruction_end; ++in )
#define UNDERSCORE "_"

using namespace llvm;
using namespace std;

map<string, int> function_names;
map<string, string> options;

vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

string tmp_dir(){
	//if(!getenv("TMPDIR")){
		return "/dev/shm/forest";
	//} else {
		//return string(getenv("TMPDIR"));
	//}
}

string tmp_file(string file){
	return tmp_dir() + "/" + file;
}


void read_options(){

	ifstream input(tmp_file("options").c_str());
	string line;
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, " ");
		options[ tokens[0] ] = tokens[1];
	}
	


}

bool cmd_option_bool(string key){
	return options[key] == "true";
}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

int cmd_option_int(string key){
	return stoi(options[key]);
}

string cmd_option_str(string key){
	return options[key];
}

string get_predicate( CmpInst* instr ){
	switch( instr->getPredicate() ){

		case CmpInst::FCMP_FALSE           : return "";
		case CmpInst::FCMP_OEQ             : return "=";
		case CmpInst::FCMP_OGT             : return ">";
		case CmpInst::FCMP_OGE             : return ">=";
		case CmpInst::FCMP_OLT             : return "<";
		case CmpInst::FCMP_OLE             : return "<=";
		case CmpInst::FCMP_ONE             : return "#";
		case CmpInst::FCMP_ORD             : return "";
		case CmpInst::FCMP_UNO             : return "";
		case CmpInst::FCMP_UEQ             : return "=";
		case CmpInst::FCMP_UGT             : return ">";
		case CmpInst::FCMP_UGE             : return ">=";
		case CmpInst::FCMP_ULT             : return "<";
		case CmpInst::FCMP_ULE             : return "<=";
		case CmpInst::FCMP_UNE             : return "#";
		case CmpInst::FCMP_TRUE            : return "";
		case CmpInst::BAD_FCMP_PREDICATE   : return "";
		case CmpInst::ICMP_EQ              : return "=";
		case CmpInst::ICMP_NE              : return "#";
		case CmpInst::ICMP_UGT             : return ">";
		case CmpInst::ICMP_UGE             : return ">=";
		case CmpInst::ICMP_ULT             : return "<";
		case CmpInst::ICMP_ULE             : return "<=";
		case CmpInst::ICMP_SGT             : return ">";
		case CmpInst::ICMP_SGE             : return ">=";
		case CmpInst::ICMP_SLT             : return "<";
		case CmpInst::ICMP_SLE             : return "<=";
		case CmpInst::BAD_ICMP_PREDICATE   : return "";
		default: assert(0 && "Unknown Operation");

	}
}

string negation(string predicate){

	if( predicate == "="  ) return "#";
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	assert(0 && "Unknown Operation");

}

void generate_static_conds(Function* fn, BasicBlock* bb, BranchInst* instr, string& cond_pos, string& cond_neg){

	CmpInst* cmp_instr = cast<CmpInst>(instr->getOperand(0));

	cond_pos = fn->getName().str() + "_" + bb->getName().str() + "." + get_predicate(cmp_instr);
	cond_neg = fn->getName().str() + "_" + bb->getName().str() + "." + negation(get_predicate(cmp_instr));

}

typedef struct Node {
	string name;
	int next_a;
	int next_b;
	string cond_a;
	string cond_b;
} Node;

int get_or_insert_node(vector<Node>& nodes, string name){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		if(nodes[i].name == name)
			return i;
	}
	
	Node node = {name, -1, -1, "", ""};
	nodes.push_back(node);
	return nodes.size()-1;
}

void set_cond(vector<Node>& nodes, int node1, int node2, string cond){

	if(nodes[node1].cond_a == ""){
		nodes[node1].cond_a = cond;
		nodes[node1].next_a = node2;
	} else {
		nodes[node1].cond_b = cond;
		nodes[node1].next_b = node2;
	}

}

vector<pair<string, string> > get_calls(map<pair<string, string>, vector<string> > calls, string function){

	vector<pair<string, string> > ret;

	for( map<pair<string, string>, vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
		string fn1 = it->first.first;
		string bb       = it->first.second;
		vector<string> callees = it->second;
		for( vector<string>::iterator it2 = callees.begin(); it2 != callees.end(); it2++ ){
			string fn2 = *it2;

			if(fn1 == function){
				pair<string, string> bb_and_fn2 = pair<string, string>(bb, fn2);
				ret.push_back(bb_and_fn2);
			}

		}
		
	}

	return ret;
	
	
}

map<string, vector<string> > get_calls_2(map<pair<string, string>, vector<string> > calls, string function){

	map<string, vector<string> > ret;

	for( map<pair<string, string>, vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
		string fn1 = it->first.first;
		string bb       = it->first.second;
		vector<string> callees = it->second;
		for( vector<string>::iterator it2 = callees.begin(); it2 != callees.end(); it2++ ){
			string fn2 = *it2;

			if(fn1 == function){
				ret[bb].push_back(fn2);
			}

		}
		
	}

	return ret;
	
	
}

int find_node_by_name(string nodename, vector<Node> nodes){
	for ( unsigned int i = 0; i < nodes.size(); i++) {
		//cerr << "nodename " << nodes[i].name << endl;
		if(nodes[i].name == nodename) return i;
	}

	cerr << nodename << endl;
	assert(0 && "Invalid node name");
}

void inline_function(string function, string nodename, map<string, map<string, map<string, string> > > conectivity_matrix, vector<Node>& nodes){
	int node_idx = find_node_by_name(nodename, nodes);

	Node node_b = nodes[node_idx];
	Node node_c = {"hola2", node_idx, -1, "true", ""};

	nodes[node_idx].name   = "hola";
	nodes[node_idx].next_a = nodes.size();
	nodes[node_idx].next_b = -1;
	nodes[node_idx].cond_a = "true";
	nodes[node_idx].cond_b = "";



	nodes.push_back(node_b);
	nodes.push_back(node_c);
	
	string name;
	//int next_a;
	//int next_b;
	string cond_a;
	string cond_b;




	//Node newnode = {"name", post_node, -1, "true", ""};

}

vector<string> filter(vector<pair<string, string> > fn_calls, string bb_1){
	vector<string> ret;

	return ret;
}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

void add_nodes(vector<Node>& ret, vector<Node> nodes, string& ini_ret, string ini_nodes, string end_nodes, string function_name, string caller_name){

	//function_names[function_name]++;

	//cerr << "ini_ret " << ini_ret << " ini_nodes " << ini_nodes << " end_nodes " << end_nodes << endl;

	int base = ret.size();



	int node_ini_ret = find_node_by_name(ini_ret,ret);

	string cond_a = ret[node_ini_ret].cond_a;
	string cond_b = ret[node_ini_ret].cond_b;
	int next_a    = ret[node_ini_ret].next_a;
	int next_b    = ret[node_ini_ret].next_b;


	for ( unsigned int i = 0; i < nodes.size(); i++) {

		string nodename = nodes[i].name + (function_names[function_name] < 2?"":("_" + itos(function_names[function_name])));
		//string nodename = nodes[i].name + "_" + itos(function_names[function_name]);
		int nodenexta = (nodes[i].next_a == -1)?-1:nodes[i].next_a + base;
		int nodenextb = (nodes[i].next_b == -1)?-1:nodes[i].next_b + base;
		string nodeconda = nodes[i].cond_a;
		string nodecondb = nodes[i].cond_b;


		Node node = { nodename, nodenexta, nodenextb, nodeconda, nodecondb };

		ret.push_back(node);
	}



	//int node_ini_nodes = find_node_by_name(ini_nodes, ret);
	//int node_end_ret = find_node_by_name(end_nodes, ret);
	int node_ini_nodes = find_node_by_name(ini_nodes, nodes) + base;
	int node_end_ret = find_node_by_name(end_nodes, nodes) + base;

	ret[node_ini_ret].next_a = node_ini_nodes;
	ret[node_ini_ret].cond_a = "true";
	ret[node_ini_ret].next_b = -1;
	ret[node_ini_ret].cond_b = "";

	ret[node_end_ret].cond_a = cond_a;
	ret[node_end_ret].cond_b = cond_b;
	ret[node_end_ret].next_a = next_a;
	ret[node_end_ret].next_b = next_b;

	ini_ret = function_name + "_return" + (function_names[function_name] < 2?"":("_" + itos(function_names[function_name])));
	//ini_ret = function_name + "_return_" + itos(function_names[function_name]);

	//cerr << "ini_ret " << ini_ret << endl;


}

vector<Node> get_nodes_fn(map<string, map<string, map<string, string> > > conectivity_matrix, map<pair<string, string>, vector<string> > calls, string function_name){
//map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
//map<pair<string, string>, vector<string> > calls; // (function and bb), functions called

	vector<Node> ret;

	map<string, map<string, string> > bbs = conectivity_matrix[function_name]; // bb1, bb2, cond
	map<string, vector<string> > fn_calls = get_calls_2(calls, function_name); // bb, fns

	for( map<string,map<string, string> >::iterator it = bbs.begin(); it != bbs.end(); it++ ){
		string bb_1 = it->first;

		//cerr << "bb " << bb_1 << endl;
		map<string, string> connected = it->second;


		for( map<string,string>::iterator it2 = connected.begin(); it2 != connected.end(); it2++ ){
			string bb_2 = it2->first;
			string cond = it2->second;
			string bb1_complete = function_name + "_" + bb_1;
			string bb2_complete = function_name + "_" + bb_2;
			int node1 = get_or_insert_node(ret, bb1_complete);
			int node2 = get_or_insert_node(ret, bb2_complete);
			set_cond(ret, node1, node2, cond);
		}

		vector<string> calls_in_bb = fn_calls[bb_1];
		bb_1 = function_name + "_" + bb_1;
		for( vector<string>::iterator it2 = calls_in_bb.begin(); it2 != calls_in_bb.end(); it2++ ){
			//cerr << "call " << bb_1 << " " << *it2 << endl;
			vector<Node> nodes = get_nodes_fn(conectivity_matrix, calls, *it2);
			add_nodes(ret, nodes, bb_1, *it2 + "_entry", *it2 + "_return", *it2, function_name);
		}




	}

	return ret;
}

string flatvec(vector<string> vectstr){
	string ret;
	for( vector<string>::iterator it = vectstr.begin(); it != vectstr.end(); it++ ){
		ret += *it;
	}

	return ret;
}

vector<Node> get_nodes_fn_rec(map<string, map<string, map<string, string> > > conectivity_matrix, map<pair<string, string>, vector<string> > calls, vector<string> function_stack, int depth){
//map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
//map<pair<string, string>, vector<string> > calls; // (function and bb), functions called

	vector<Node> ret;

	if(depth > cmd_option_int("heuristic_recursive_depth")) return ret;

	string function_name = function_stack[function_stack.size() - 1];
	map<string, map<string, string> > bbs = conectivity_matrix[function_name]; // bb1, bb2, cond
	map<string, vector<string> > fn_calls = get_calls_2(calls, function_name); // bb, fns

	for( map<string,map<string, string> >::iterator it = bbs.begin(); it != bbs.end(); it++ ){
		string bb_1 = it->first;

		//cerr << "bb " << bb_1 << endl;
		map<string, string> connected = it->second;

		map<string, string> connected2;
		for( map<string,string>::iterator it2 = connected.begin(); it2 != connected.end(); it2++ ){
			if(it2->second.find(".") != string::npos)
				connected2[it2->first] = flatvec(function_stack) + "_" + tokenize(it2->second, "._")[1] + "." + tokenize(it2->second, ".")[1];
			else
				connected2[it2->first] = it2->second;
		}
		connected = connected2;
		

		for( map<string,string>::iterator it2 = connected.begin(); it2 != connected.end(); it2++ ){
			string bb_2 = it2->first;
			string cond = it2->second;
			string bb1_complete = flatvec(function_stack) + "_" + bb_1;
			string bb2_complete = flatvec(function_stack) + "_" + bb_2;
			int node1 = get_or_insert_node(ret, bb1_complete);
			int node2 = get_or_insert_node(ret, bb2_complete);
			set_cond(ret, node1, node2, cond);
		}

		vector<string> calls_in_bb = fn_calls[bb_1];
		bb_1 = flatvec(function_stack) + "_" + bb_1;
		for( vector<string>::iterator it2 = calls_in_bb.begin(); it2 != calls_in_bb.end(); it2++ ){
			//cerr << "call " << bb_1 << " " << *it2 << endl;
			vector<string> callstack2 = function_stack; callstack2.push_back(*it2);
			vector<Node> nodes = get_nodes_fn_rec(conectivity_matrix, calls, callstack2, depth + 1);
			if(depth != cmd_option_int("heuristic_recursive_depth"))
			add_nodes(ret, nodes, bb_1, flatvec(callstack2) + "_entry", flatvec(callstack2) + "_return", flatvec(callstack2), function_name);
		}




	}

	return ret;
}

map<string, map<string, string> > inline_calls( map<string, map<string, map<string, string> > > conectivity_matrix, map<pair<string, string>, vector<string> > calls ){
// bb1, bb2, cond
//map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
//map<pair<string, string>, vector<string> > calls; // (function and bb), functions called

	map<string, map<string, string> > ret;
	vector<Node> nodes = get_nodes_fn(conectivity_matrix, calls, "main");

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		string name1 = nodes[i].name;

		bool has_next_a = (nodes[i].next_a != -1);
		bool has_next_b = (nodes[i].next_b != -1);

		if(has_next_a){
			string name2 = nodes[nodes[i].next_a].name;
			string cond = nodes[i].cond_a;
			ret[name1][name2] = cond;
		}

		if(has_next_b){
			string name2 = nodes[nodes[i].next_b].name;
			string cond = nodes[i].cond_b;
			ret[name1][name2] = cond;
		}


	}
	
	return ret;

}

map<string, map<string, string> > inline_calls_rec( map<string, map<string, map<string, string> > > conectivity_matrix, map<pair<string, string>, vector<string> > calls ){
// bb1, bb2, cond
//map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
//map<pair<string, string>, vector<string> > calls; // (function and bb), functions called

	map<string, map<string, string> > ret;
	vector<string> function_stack; function_stack.push_back("main");
	vector<Node> nodes = get_nodes_fn_rec(conectivity_matrix, calls, function_stack, 0);

	for ( unsigned int i = 0; i < nodes.size(); i++) {
		string name1 = nodes[i].name;

		bool has_next_a = (nodes[i].next_a != -1);
		bool has_next_b = (nodes[i].next_b != -1);

		if(has_next_a){
			string name2 = nodes[nodes[i].next_a].name;
			string cond = nodes[i].cond_a;
			ret[name1][name2] = cond;
		}

		if(has_next_b){
			string name2 = nodes[nodes[i].next_b].name;
			string cond = nodes[i].cond_b;
			ret[name1][name2] = cond;
		}


	}
	
	return ret;

}

map<string, int> get_name_to_node( map<string, map<string, string> > conectivity_matrix_inlined ){

	map<string, int> ret;
	set<string> names;

	for( map<string, map<string, string> >::iterator it = conectivity_matrix_inlined.begin(); it != conectivity_matrix_inlined.end(); it++ ){
		string name1 = it->first;
		names.insert(name1);

		map<string, string> mapsecond = it->second;
		for( map<string,string>::iterator it2 = mapsecond.begin(); it2 != mapsecond.end(); it2++ ){
			string name2 = it2->first;
			names.insert(name2);
		}
		
		
	}

	int n = 0;
	for( set<string>::iterator it = names.begin(); it != names.end(); it++ ){
		ret[*it] = n++;
	}

	ret["main_return"] = names.size();

	return ret;

}

void gen_graph_file(map<string, map<string, string> > conectivity_matrix_inlined, map<string, int> name_to_node){

	//cerr << "gen_graph_file" << endl;
	
	int max_node = 0;
	for( map<string,int>::iterator it = name_to_node.begin(); it != name_to_node.end(); it++ ){
		int node = it->second;
		if(node > max_node) max_node = node;
	}
	max_node ++;
	
	

	FILE* graph_file = fopen(tmp_file("graph").c_str(), "w");

	fprintf(graph_file, "%lu\n\n", max_node);

	set<int> used_nodes;


	for( map<string, map<string, string> >::iterator it2 = conectivity_matrix_inlined.begin(); it2 != conectivity_matrix_inlined.end(); it2++ ){
		string bb_1 = it2->first;
		map<string, string> connected = it2->second;
		for( map<string,string>::iterator it3 = connected.begin(); it3 != connected.end(); it3++ ){
			string bb_2 = it3->first;

			fprintf(graph_file, "%d %d 1\n", name_to_node[bb_1], name_to_node[bb_2]);

			used_nodes.insert(name_to_node[bb_1]);
			used_nodes.insert(name_to_node[bb_2]);

		}

	}

	for ( unsigned int i = 0; i < max_node; i++) {
		if(used_nodes.find(i) == used_nodes.end()){
			fprintf(graph_file, "%d %d 1\n", i, i);
		}
	}

	fclose(graph_file);
	
}

map<int, string> inverse(map<string, int> name_to_node){
	map<int, string> ret;

	for( map<string,int>::iterator it = name_to_node.begin(); it != name_to_node.end(); it++ ){
		string name = it->first;
		int    node = it->second;
		ret[node] = name;
	}

	return ret;
	
}

vector<string> get_edges(vector<int> path, map<int, string> node_to_name, map<string, map<string, string> > conectivity_matrix_inlined ){

	vector<string> ret;

	for ( unsigned int i = 0; i < path.size()-1; i++) {
		int node1 = path[i];
		int node2 = path[i+1];
		string node1_s = node_to_name[node1];
		string node2_s = node_to_name[node2];

		string cond = conectivity_matrix_inlined[node1_s][node2_s];

		//cerr << cond << endl;

		ret.push_back(cond);

	}

	return ret;

}

struct PathFinder: public ModulePass {

	static char ID;
	PathFinder() : ModulePass(ID) {}
	virtual bool runOnModule(Module &M) {

		read_options();

		map<string, map<string, string> > conectivity_matrix_inlined; // bb1, bb2, cond
		map<string, map<string, map<string, string> > > conectivity_matrix; // function, bb1, bb2, cond 
		map<pair<string, string>, vector<string> > calls; // (function and bb), functions called


		mod_iterator(M, fun){
		fun_iterator(fun,bb){

			string fn_name = fun->getName().str(); if(fn_name[0] == '_') fn_name = fn_name.substr(1);
			string bb_name =  bb->getName().str();

			Instruction* term = bb->getTerminator();
			//term->dump();
			if( BranchInst::classof(term) ){

				BranchInst* in_b = cast<BranchInst>(term);
				if(in_b->isConditional()){
					//cerr << "conditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();
					string name2 = in_b->getSuccessor(1)->getName().str();

					string cond_pos;
					string cond_neg;
					generate_static_conds(fun, bb, in_b, cond_pos, cond_neg);

					conectivity_matrix[fn_name][bb_name][name1] = cond_pos;
					conectivity_matrix[fn_name][bb_name][name2] = cond_neg;


				} else {
					//cerr << "inconditional" << endl;

					string name1 = in_b->getSuccessor(0)->getName().str();
					conectivity_matrix[fn_name][bb_name][name1] = "true";
					
				}

			}

		}}


		

		mod_iterator(M, fun){
		fun_iterator(fun,bb){
		blk_iterator(bb, in){
			if(CallInst::classof(in)){
				CallInst* in_c = cast<CallInst>(in);

				string fun_1 = fun->getName().str();
				string bb_1  = bb->getName().str();
				string fun_2 = in_c->getCalledFunction()->getName().str();

				if(fun_1[0] == '_') fun_1 = fun_1.substr(1);
				if(fun_2[0] == '_') fun_2 = fun_2.substr(1);


				calls[pair<string, string>(fun_1, bb_1)].push_back(fun_2);
			}
		}}}


		//for( map<pair<string, string>,vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
			//pair<string, string> src = it->first;
			//vector<string> dst = it->second;

			//for( vector<string>::iterator it2 = dst.begin(); it2 != dst.end(); it2++ ){
				//cerr << src.first << "-" << src.second << ":" << *it2 << endl;
			//}
			
			
		//}


		if(cmd_option_bool("recursive"))
			conectivity_matrix_inlined = inline_calls_rec(conectivity_matrix, calls);
		else
			conectivity_matrix_inlined = inline_calls(conectivity_matrix, calls);

		map<string, int> name_to_node = get_name_to_node(conectivity_matrix_inlined);
		map<int, string> node_to_name = inverse(name_to_node);
		gen_graph_file(conectivity_matrix_inlined, name_to_node);



		FILE* file;

		file = fopen(tmp_file("connectivity_matrix_inlined").c_str(), "w");
		for( map<string,map<string,string> >::iterator it = conectivity_matrix_inlined.begin(); it != conectivity_matrix_inlined.end(); it++ ){
			string bb1 = it->first;
			map<string, string> bb2_bb3 = it->second;
			for( map<string,string>::iterator it2 = bb2_bb3.begin(); it2 != bb2_bb3.end(); it2++ ){
				string bb2 = it2->first;
				string bb3 = it2->second;
				fprintf(file, "%s %s %s\n", bb1.c_str(), bb2.c_str(), bb3.c_str());
			}
		}
		fclose(file);
		
		file = fopen(tmp_file("connectivity_matrix").c_str(), "w");
		for( map<string, map<string, map<string, string> > >::iterator it = conectivity_matrix.begin(); it != conectivity_matrix.end(); it++ ){
			string function = it->first;
			map<string, map<string, string> > bb1_bb2_cond = it->second;
			for( map<string, map<string, string> >::iterator it2 = bb1_bb2_cond.begin(); it2 != bb1_bb2_cond.end(); it2++ ){
				string bb1 = it2->first;
				map<string, string> bb2_cond = it2->second;
				for( map<string,string>::iterator it3 = bb2_cond.begin(); it3 != bb2_cond.end(); it3++ ){
					string bb2 = it3->first;
					string cond = it3->second;
					fprintf(file, "%s %s %s %s\n", function.c_str(), bb1.c_str(), bb2.c_str(), cond.c_str());
				}
			}
		}
		fclose(file);
		
		file = fopen(tmp_file("calls").c_str(), "w");
		for( map<pair<string, string>, vector<string> >::iterator it = calls.begin(); it != calls.end(); it++ ){
			string function = it->first.first;
			string bb       = it->first.second;
			vector<string> functions_called = it->second;
			for( vector<string>::iterator it2 = functions_called.begin(); it2 != functions_called.end(); it2++ ){
				string function_called = *it2;
				printf("%s %s %s\n", function.c_str(), bb.c_str(), function_called.c_str());
			}
		}
		fclose(file);


		//for( map<string,int>::iterator it = name_to_node.begin(); it != name_to_node.end(); it++ ){
			//cerr << it->first << " " << it->second << endl;
		//}
		

		Graph my_graph(tmp_file("graph").c_str());

		string target_node_s = cmd_option_str("target_node");

		int target_node_i  = name_to_node[target_node_s];

		//cerr << "target_node " << target_node_s << " " << target_node_i << endl;

		YenTopKShortestPathsAlg yenAlg(my_graph, my_graph.get_vertex(name_to_node["main_entry"]), my_graph.get_vertex(target_node_i));

		set<string> conditions_set;

		int count = 0;
		while(true) {

			if(!yenAlg.has_next()) break;
			if( count > cmd_option_int("max_heuristic_paths") ) break;

			count++;
			//cerr << "yenAlg" << endl;
			//yenAlg.next()->PrintOut(cerr);
			vector<int> path = yenAlg.next()->get_vector();
			vector<string> conditions = get_edges(path, node_to_name, conectivity_matrix_inlined );

			//for( vector<int>::iterator it = path.begin(); it != path.end(); it++ ){
				//cerr << node_to_name[*it] << ",";
			//}
			//cerr << endl;
			
			for( vector<string>::iterator it = conditions.begin(); it != conditions.end(); it++ ){
				if(*it != "true") conditions_set.insert(*it);
			}
		}

		FILE* file_heuristics = fopen(tmp_file("heuristics").c_str(), "w");
		for( set<string>::iterator it = conditions_set.begin(); it != conditions_set.end(); it++ ){
			fprintf(file_heuristics, "%s\n", ((*it)[0]=='_')?it->substr(1).c_str():it->c_str());
		}
		fclose(file_heuristics);
		



		FILE* file_dot = fopen(tmp_file("pathfinder.dot").c_str(), "w");
		fprintf(file_dot, "digraph G {\n");

		for( map<string, map<string, string> >::iterator it2 = conectivity_matrix_inlined.begin(); it2 != conectivity_matrix_inlined.end(); it2++ ){
			string bb_1 = it2->first;
			map<string, string> connected = it2->second;
			for( map<string,string>::iterator it3 = connected.begin(); it3 != connected.end(); it3++ ){
				string bb_2 = it3->first;

				string bb1_complete = bb_1 + "_" + itos(name_to_node[bb_1]);
				string bb2_complete = bb_2 + "_" + itos(name_to_node[bb_2]);
				string label = conectivity_matrix_inlined[bb_1][bb_2];

				string color = (conditions_set.find(label)!=conditions_set.end())?",color=red":"";

				fprintf(file_dot, "%s -> %s [label=\"%s\"%s]\n", bb1_complete.c_str(), bb2_complete.c_str(), label.c_str(), color.c_str() );

			}

		}
			
		fprintf(file_dot, "}\n");
		fclose(file_dot);
		
		if(cmd_option_bool("show_heuristic_graph"))
		int ret = system(("cd " + tmp_dir() + "; cat pathfinder.dot | dot -Tpng > pathfinder.png; eog pathfinder.png;").c_str());


		return false;
	}
};

char PathFinder::ID = 0;
static RegisterPass<PathFinder> PathFinder( "pathfinder", "Finds static paths to target");

