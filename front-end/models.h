/*
 * =====================================================================================
 * /
 * |     Filename:  models.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 06:15:37 PM
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

#ifndef _MODELS_H_
#define _MODELS_H_

#include <vector>
#include <string>
#include <set>
#include <sstream>
#include "cmd_options.h"

using namespace std;


typedef struct Node {
	string cond_pos;
	int node_pos;
	int node_neg;
	string assign;
} Node;

typedef struct ParentStruct {
	string branch;
	int node;
} ParentStruct;

typedef vector<string> Path;


typedef struct PathAndAssign {
	Path path;
	string assign;
} PathAndAssign;



vector<string> get_model_paths();
vector<string> get_model_assigns();
vector<string> get_model_names();
set<string> get_model_freevars();
set<string> get_model_outputs();
void and_paths(vector<string>& paths);
void get_model();
void get_model_modelfinder();

vector<ParentStruct> get_parents(vector<Node> nodes, int n);

void pass_1(vector<Node>& nodes);
void pass_2(vector<Node>& nodes);
void pass_3(vector<Node>& nodes);

void rm_invalid_nodes(vector<Node>& nodes);
void robdd(vector<Node>& nodes);

void get_model_fn();
void normalize(PathAndAssign& path_and_assign);
void normalize(vector<PathAndAssign>& path_and_assigns);
string get_ite_expr(vector<Node> nodes, int n = 0);
set<string> get_set_variables(vector<PathAndAssign> path_and_assigns);
void make_tree(vector<Node>& nodes, vector<PathAndAssign> paths_and_assign, vector<string> cond_ordering , int depth = 0);
void show_bdd(vector<Node> nodes, string title = "");
string negation(string cond);
void add_path(vector<Node>& nodes, PathAndAssign path_and_assign, int node_root = 0);
bool is_complete(string variable, vector<PathAndAssign> table);
void part_paths(string cond, vector<PathAndAssign> input, vector<PathAndAssign>& output_pos, vector<PathAndAssign>& output_neg );
PathAndAssign get_to_front(PathAndAssign path_and_assign, string cond_pos, int depth);
void get_to_front(vector<PathAndAssign>& path_and_assigns, string cond_pos, int depth);
vector<string> remove(vector<string>input , string to_remove);
string positive_cond(string condition);
void insert_node(vector<Node>& nodes, Node node);
PathAndAssign tail(PathAndAssign path_and_assign);
void new_node_pos(vector<Node>& nodes, int node_root);
void new_node_neg(vector<Node>& nodes, int node_root);
bool contains_pos(Path path, string cond);
bool contains_neg(Path path, string cond);
Path put_nth(string cond, Path path, int depth);
void permute(vector<string>& variables_vec);
void print_path_assign(PathAndAssign pa);
void print_path(Path path);


#endif /* end of include guard: _MODELS_H_ */
