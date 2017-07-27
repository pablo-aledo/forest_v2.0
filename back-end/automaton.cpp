/*
 * =====================================================================================
 * /
 * |     Filename:  automaton.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2014 02:36:33 PM
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

#include "automaton.h"

Automaton::Automaton(){
	
}

Automaton::Automaton(string filename){
	load_from_file(filename);
}

Automaton::~Automaton(){
	
}

void Automaton::load_from_file(string filename){

	printf("Automaton::load_from_file\n");

	ifstream input(filename.c_str());
	string line;
	
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, " ");
		Transition transition = {tokens[0], tokens[1], tokens[2]};
		transitions.push_back(transition);
	}

}

void Automaton::show_automaton(){

	printf("Automaton::show_automaton\n");

	FILE* file = fopen(tmp_file("digraph").c_str(), "w");
	fprintf(file, "digraph G{\n");
	for ( unsigned int i = 0; i < transitions.size(); i++) {

		string origin = transitions[i].origin;
		string dest   = transitions[i].dest;
		string cond   = transitions[i].condition;

		fprintf(file, "%s -> %s [label=\"%s\"]\n", origin.c_str(), dest.c_str(), cond.c_str() );

	}

	fprintf(file, "}\n");
	fclose(file);
	system(("cat " + tmp_file("digraph") + " | dot -Tpng > " + tmp_file("digraph.png") + " 2>/dev/null").c_str());
	system(("eog " + tmp_file("digraph.png")+ " 2>/dev/null").c_str());

}

void Automaton::set_state(string _state){
	state = _state;
}

string Automaton::get_state(){
	return state;
}

void Automaton::advance_trues(string& state){
	for( vector<Transition>::iterator it = transitions.begin(); it != transitions.end(); it++ ){
		if(it->origin == state && it->condition == "true"){
			state = it->dest;
			advance_trues(state);
			return;
		}
	}
}

string Automaton::dst_state_for_transition(string state, string transition){

	//printf("dst_state_for_transition %s %s\n", state.c_str(), transition.c_str());

	advance_trues(state);

	for( vector<Transition>::iterator it = transitions.begin(); it != transitions.end(); it++ ){


		if(it->origin == state && it->condition == transition){
			string state_aux = it->dest;
			advance_trues(state_aux);
			return state_aux;
		}
	}

	return "sink_state";
	
}

void Automaton::advance(string transition){

	string state_prev = state;
	string state_post = dst_state_for_transition(state_prev, transition);
	state = state_post;

	//printf("advance from %s to %s\n", state_prev.c_str(), state_post.c_str());

}

set<string> Automaton::get_possible_transitions(){
	set<string> ret;

	for( vector<Transition>::iterator it = transitions.begin(); it != transitions.end(); it++ ){


		if(it->origin == state){
			ret.insert(it->condition);
		}
	}

	return ret;
}

