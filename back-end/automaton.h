/*
 * =====================================================================================
 * /
 * |     Filename:  automaton.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/30/2014 02:36:46 PM
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


#ifndef _AUTOMATON_H_
#define _AUTOMATON_H_

#include <string>
#include <fstream>
#include <vector>
#include <set>
#include "utils.h"
#include <stdlib.h>

using namespace std;


typedef struct Transition{
	string origin;
	string condition;
	string dest;
} Transition;

class Automaton {
public:
	set<string> get_possible_transitions();
	string get_state();
	void advance(string transition);
	void set_state(string _state);
	void show_automaton();
	Automaton();
	virtual ~Automaton ();
	void load_from_file(string filename);
	Automaton(string);
private:
	void advance_trues(string& state);

	string dst_state_for_transition(string state, string transition);
	vector<Transition> transitions;
	string state;
	
};

#endif /* end of include guard: _AUTOMATON_H_ */

