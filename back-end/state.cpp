/*
 * =====================================================================================
 * /
 * |     Filename:  state.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/22/2014 07:41:17 PM
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


#include "state.h"


State::State(){
	
}

State::~State(){
	
}

State::State(vector<Assignment> _assignments, string _condition, string _bb){
	assignments = _assignments;
	condition   = _condition;
	bb          = _bb;

}


vector<Assignment> State::get_assignments(){

	return assignments;

}


string State::get_condition(){

	return condition;

}

string State::get_bb(){

	return bb;

}

