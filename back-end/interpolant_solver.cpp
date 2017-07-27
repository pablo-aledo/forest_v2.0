/*
 * =====================================================================================
 * /
 * |     Filename:  interpolant_solver.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  09/19/2014 04:58:40 AM
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

#include "interpolant_solver.h"

extern Operators* operators;
extern Database*  database;
extern Options*   options;

InterpolantSolver::InterpolantSolver(){

	z3solver = new Z3RealInt();

	program_automaton.load_from_file(tmp_file("program_automaton").c_str());
	//program_automaton.show_automaton();

	system(("ls " + tmp_file("rejecting_automaton_*") + " > " + tmp_file("rejecting_automatons")).c_str());

	ifstream input(tmp_file("rejecting_automatons").c_str());
	string line;
	while( getline( input, line ) ) {
		Automaton rejecting_automaton(line);
		//rejecting_automaton.show_automaton();
		rejecting_automatons.push_back(rejecting_automaton);
	}

}

void InterpolantSolver::push_condition_var(string name, bool invert ){

	last_bb = bb_name(operators->get_actual_function() + "_" + operators->get_actual_bb());

	if(name == ""){
		pairs_bb_condition.push_back(pair<string, string>(last_bb, "true"));
		return;
	}


	last_condition = condition_of(last_dst_content);
	stack_of_conditions.push_back(operators->get_actual_function() + "_" + operators->get_actual_bb() + "." + last_condition);
	printf("\e[32m InterpolantSolver::push_condition_var \e[0m %s %s %s\n", last_bb.c_str(), last_dst_content.c_str(), last_condition.c_str());


	last_indicator = realvalue(name)=="true"?"F":"T";

	pairs_bb_condition.push_back(pair<string, string>(last_bb, last_dst_content));

	z3solver->get_context(this);
	z3solver->push_condition_var(name, invert );
	get_context_back(z3solver);
}

void InterpolantSolver::assign_instruction_content(string src, string dst, string fn_name){



	z3solver->get_context(this);
	z3solver->assign_instruction_content(src,dst, fn_name);
	get_context_back(z3solver);

	last_dst = dst;
	last_dst_content = z3solver->content_smt(dst);

	//printf("assign_instruction %s %s\n", dst.c_str(), last_dst_content.c_str());
}

void InterpolantSolver::binary_instruction_content(string dst, string op1, string op2, string operation){


	z3solver->get_context(this);
	z3solver->binary_instruction_content(dst, op1, op2, operation);
	get_context_back(z3solver);

	last_dst = dst;
	last_dst_content = z3solver->content_smt(dst);

	//printf("binary_instruction %s %s\n", dst.c_str(), last_dst_content.c_str());

}

void InterpolantSolver::solve_problem(){

	if(problem_in_interpolant_state()){
		is_in_interpolant = true;
		return;
	} else {
		is_in_interpolant = false;
	}




	z3solver->get_context(this);
	z3solver->solve_problem();
	get_context_back(z3solver);

	if(! z3solver->solvable_problem()){
		printf("\e[32m Infeasible, calculate_interpolants \e[0m\n");
		calculate_interpolants();
	} else {
		printf("\e[32m Feasible, dont calculate_interpolants \e[0m\n");
	}

}

void InterpolantSolver::set_sat(bool _sat){


	if(!_sat){
		printf("\e[32m set_sat infeasible, calculate_interpolants \e[0m\n");
		calculate_interpolants();
	}

	z3solver->get_context(this);
	z3solver->set_sat(_sat);
	get_context_back(z3solver);
}

void InterpolantSolver::calculate_interpolants(){


	for( vector<pair<string, string> >::iterator it = pairs_bb_condition.begin(); it != pairs_bb_condition.end(); it++ ){
		printf("pair_bb_condition %s %s\n", it->first.c_str(), it->second.c_str());
	}

	FILE* interpolants_file = fopen(tmp_file("interpolants.smt2").c_str(), "w");
	dump_header(interpolants_file);
	z3solver->dump_variables(interpolants_file);
	dump_interpolants(interpolants_file);
	z3solver->dump_check_sat(interpolants_file);
	dump_get_interpolants(interpolants_file);
	fclose(interpolants_file);

	system(("iz3 " + tmp_file("interpolants.smt2") + " > " + tmp_file("interpolants_out")).c_str());

	vector<string> interpolants;
	ifstream input(tmp_file("interpolants_out").c_str());
	string line; getline(input, line);
	assert(line == "unsat" && "Interpolants of sat solution");
	while( getline( input, line ) ) {
		interpolants.push_back(line);
	}


	vector<string> bbs;
	for( vector<pair<string, string> >::iterator it = pairs_bb_condition.begin(); it != pairs_bb_condition.end(); it++ ){
		bbs.push_back(it->first);
	}
	
	vector<string> conditions;
	for( vector<pair<string, string> >::iterator it = pairs_bb_condition.begin(); it != pairs_bb_condition.end(); it++ ){
		conditions.push_back(it->second);
	}

	generate_rejecting_automaton(bbs,conditions, interpolants);

	getchar();
	
}

void InterpolantSolver::generate_rejecting_automaton(vector<string> bbs,vector<string> conditions, vector<string> interpolants){

	assert(bbs.size() == conditions.size());
	assert(bbs.size()-1 == interpolants.size());

	bool loop_found = 0;
	vector<Triple> rejecting_automaton;

	for ( unsigned int i = 0; i < bbs.size()-1; i++) {
		vector<string> tokens = tokenize(bbs[i], "_");
		string condition = tokens[0] + "_" + tokens[1] + "." + condition_of(conditions[i]);
		Triple triple = {bbs[i], condition, bbs[i+1]};
		rejecting_automaton.push_back(triple);
	}


	map<string, int> number_of_bbs;
	for ( unsigned int i = 0; i < bbs.size(); i++) {
		vector<string> tokens = tokenize(bbs[i], "_");
		string bb = tokens[0] + "_" + tokens[1];
		int number = stoi(tokens[2])+1;
		number_of_bbs[bb] = number;
	}

	for( map<string,int>::iterator it = number_of_bbs.begin(); it != number_of_bbs.end(); it++ ){
		printf("number_of_bbs %s %d\n", it->first.c_str(), it->second);
		if(it->second > 1){
			for ( unsigned int i = 0; i < it->second-1; i++) {
				int n_first = id_of(bbs, it->first + "_" + itos(i) );
				int n_connected = n_first + 1;
				string name_connected = bbs[n_connected];
				string name_second = it->first + "_" + itos(it->second-1);
				string interpolant_second = interpolants[n_first];
				string interpolant_connected = interpolants[n_connected];
				vector<string> tokens = tokenize(name_second, "_");
				string condition = tokens[0] + "_" + tokens[1] + "." + condition_of(conditions[i]);

				if(check_inclusion(interpolant_second, interpolant_connected)){
					change_polarity(rejecting_automaton, name_second );
					Triple triple = {name_second, condition, name_connected};
					rejecting_automaton.push_back(triple);
					loop_found = 1;
				}
			}
		}
	}


	if(loop_found){
		string filename = tmp_file("rejecting_automaton_") + itos(rand());
		FILE* file = fopen(filename.c_str(), "w");

		for( vector<Triple>::iterator it = rejecting_automaton.begin(); it != rejecting_automaton.end(); it++ ){
			string med = it->str2;
			if(med.substr(med.length()-4) == "true") med = "true";
			fprintf(file, "%s %s %s\n", it->str1.c_str(), med.c_str(), it->str3.c_str() );
		}
		
		fclose(file);
	}

}

void InterpolantSolver::change_polarity(vector<Triple>& rejecting_automaton, string basic_block){


	for( vector<Triple>::iterator it = rejecting_automaton.begin(); it != rejecting_automaton.end(); it++ ){
		if(it->str1 == basic_block){
			vector<string> tokens = tokenize(it->str2, ".");
			it->str2 = tokens[0] + "." + negate_polarity(tokens[1]);
			return;
		}
	}

	printf("bb %s\n", basic_block.c_str());

	assert(0 && "Basic block not found");
	

}

bool InterpolantSolver::check_inclusion(string interpolant_second, string interpolant_connected){
	return true;
}

int InterpolantSolver::id_of(vector<string> bbs, string name){
	for ( unsigned int i = 0; i < bbs.size(); i++) {
		if(bbs[i] == name) return i;
	}

	assert(0 && "Not found");
}

void InterpolantSolver::dump_header(FILE* file){

	fprintf(file, "(set-option :produce-interpolants true)\n");

}

void InterpolantSolver::dump_get_interpolants(FILE* file){

	fprintf(file, "(get-interpolant");

	for( vector<pair<string, string> >::iterator it = pairs_bb_condition.begin(); it != pairs_bb_condition.end(); it++ ){
		fprintf(file, " %s", it->first.c_str());
	}

	fprintf(file, ")\n");

	
}

void InterpolantSolver::dump_interpolants(FILE* file){


	for( vector<pair<string, string> >::iterator it = pairs_bb_condition.begin(); it != pairs_bb_condition.end(); it++ ){
		fprintf(file, "(assert (! %s :named %s))\n", z3solver->internal_condition(it->second).c_str(), it->first.c_str());
	}
}

bool InterpolantSolver::problem_in_interpolant_state(){

	string position = operators->get_actual_function() + "_" + operators->get_actual_bb();
	string path_last = get_path_stack_str() + last_indicator;

	printf("\e[32m Problem_in_interpolant_state \e[0m position %s stack_of_conditions %lu\n",position.c_str(), stack_of_conditions.size());

	for ( unsigned int i = 0; i < stack_of_conditions.size(); i++) {
		printf("\e[32m condition \e[0m %s\n", stack_of_conditions[i].c_str());
	}


	
	program_automaton.set_state(position);
	for( vector<Automaton>::iterator it = rejecting_automatons.begin(); it != rejecting_automatons.end(); it++ ){
		it->set_state("main_entry_0");
		for( vector<string>::iterator it2 = stack_of_conditions.begin(); it2 != stack_of_conditions.end(); it2++ ){
			it->advance(*it2);
		}
	}


	printf("\e[32m program_automaton state \e[0m   %s\n", program_automaton.get_state().c_str());
	printf("\e[32m rejecting_automaton state \e[0m %s\n", rejecting_automatons.size()?rejecting_automatons[0].get_state().c_str():"");


	printf("\e[32m Problem_in_interpolant_state \e[0m %s %s\n", position.c_str(), path_last.c_str());

	if(!rejecting_automatons.size()){
		printf("\e[32m No rejecting automatons \e[0m\n");
		return false;
	}

	vector<Automaton> vector_automatons;

	vector_automatons.push_back(program_automaton);
	for( vector<Automaton>::iterator it = rejecting_automatons.begin(); it != rejecting_automatons.end(); it++ ){
		vector_automatons.push_back(*it);
	}

	vector<vector<Automaton> > matrix_automaton;
	matrix_automaton.push_back(vector_automatons);

	vector<vector<string> > rejecting_information;

	while(true){

		printf("matrix_automaton.size() %lu\n", matrix_automaton.size() );
		if(!matrix_automaton.size()) break;

		//printf("\e[32m matrix_automatons_prev \e[0m\n");
		//show_matrix_automatons(matrix_automaton);

		vector<Automaton> last_vector = matrix_automaton[matrix_automaton.size()-1];
		int n_to_remove = matrix_automaton.size()-1;
		vector<vector<Automaton> > new_automatons = iterate_transitions(last_vector);

		for( vector<vector<Automaton> >::iterator it = new_automatons.begin(); it != new_automatons.end(); it++ ){
			if(!is_in_matrix(*it, matrix_automaton))
				matrix_automaton.push_back(*it);
		}

		printf("\e[32m new_automatons \e[0m\n");
		show_matrix_automatons(new_automatons);
		printf("\e[32m matrix_automatons_post \e[0m\n");
		show_matrix_automatons(matrix_automaton);


		vector<string> states = rejecting_automaton_states( matrix_automaton[n_to_remove] );
		if(states.size())
			rejecting_information.push_back(states);


		matrix_automaton.erase(matrix_automaton.begin() + n_to_remove);


		printf("\e[32m state fully explored\e[0m\n");
		show_matrix_automatons(matrix_automaton);

	}

	printf("\e[32m Rejecting_states \e[0m\n");
	for( vector<vector<string> >::iterator it = rejecting_information.begin(); it != rejecting_information.end(); it++ ){
		vector<string> row = *it;
		for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
			printf("%s ", it2->c_str());
		}
		printf("\n");
	}
	

	if(all_terminations_are_rejected(rejecting_information))
		return true; // you can prune the subtree
	else
		return false; // you can't prune the subtree

}

vector<vector<Automaton> > InterpolantSolver::iterate_transitions( vector<Automaton> vector_automatons){

	vector<vector<Automaton> > ret;

	vector<set<string> > possible_transitions = get_possible_transitions(vector_automatons);
	set<vector<string> > result;
	vector<string> actual;
	get_combination_of_transitions( possible_transitions, result, actual );

	result = filter_combination_of_transitions( result );

	print_possible_tansitions(possible_transitions);
	//print_possible_combinations(result);

	for( set<vector<string> >::iterator it = result.begin(); it != result.end(); it++ ){

		vector<string> transitions = *it;
		vector<Automaton> vector_new = vector_automatons;

		for ( unsigned int i = 0; i < transitions.size(); i++) {
			vector_new[i].advance(transitions[i]);
		}

		ret.push_back(vector_new);
	}

	//print_states(ret);

	return ret;

}

vector<set<string> > InterpolantSolver::get_possible_transitions(vector<Automaton> vector_automatons){

	vector<set<string> > ret;
	for( vector<Automaton>::iterator it = vector_automatons.begin(); it != vector_automatons.end(); it++ ){
		set<string> possible_transitions_single = it->get_possible_transitions();
		ret.push_back(possible_transitions_single);
	}
	

	return ret;
}

void InterpolantSolver::get_combination_of_transitions( vector<set<string> > possible_transitions, set<vector<string> >& result, vector<string> actual ){

	if(!possible_transitions.size()){
		result.insert(actual);
		return;
	}

	set<string> first_column = possible_transitions[0];
	vector<set<string> > new_input = possible_transitions; new_input.erase(new_input.begin());
	
	for( set<string>::iterator it = first_column.begin(); it != first_column.end(); it++ ){
		vector<string> new_actual = actual;
		new_actual.push_back(*it);
		get_combination_of_transitions(new_input, result,new_actual);
	}
	
	

}

set<vector<string> > InterpolantSolver::filter_combination_of_transitions( set<vector<string> > input){

	set<vector<string> > ret;

	for( set<vector<string> >::iterator it = input.begin(); it != input.end(); it++ ){
		vector<string> vector_states = *it;
		if(is_valid_vector_states(vector_states)) ret.insert(*it);
	}

	return ret;
	
}

bool InterpolantSolver::is_valid_vector_states(vector<string> input){

	for( vector<string>::iterator it1 = input.begin(); it1 != input.end(); it1++ ){
		for( vector<string>::iterator it2 = input.begin(); it2 != input.end(); it2++ ){
			string tok1 = tokenize(*it1, ".")[0];
			string tok2 = tokenize(*it2, ".")[0];
			string sig1 = tokenize(*it1, ".")[1];
			string sig2 = tokenize(*it2, ".")[1];

			if(tok1 == tok2 && sig1 != sig2) return false;
		}
	}

	return true;
	
}

bool InterpolantSolver::is_in_matrix(vector<Automaton> vector_aut, vector<vector<Automaton> > matrix_aut){

	vector<string> states_vector = get_states(vector_aut);

	for( vector<vector<Automaton> >::iterator it = matrix_aut.begin(); it != matrix_aut.end(); it++ ){
		vector<string> states_matrix = get_states( *it );
		if(states_matrix == states_vector ) return true;

	}
	
	return false;

}

vector<string> InterpolantSolver::get_states(vector<Automaton> vector_aut){
	
	vector<string> ret;

	for( vector<Automaton>::iterator it = vector_aut.begin(); it != vector_aut.end(); it++ ){
		ret.push_back(it->get_state());
	}

	return ret;
	
}

void InterpolantSolver::show_matrix_automatons(vector<vector<Automaton> > matrix_automaton){

	//printf("\e[32m matrix_automatons \e[0m\n");

	for( vector<vector<Automaton> >::iterator it = matrix_automaton.begin(); it != matrix_automaton.end(); it++ ){
		vector<Automaton> vector_automatons = *it;
		for( vector<Automaton>::iterator it2 = vector_automatons.begin(); it2 != vector_automatons.end(); it2++ ){
			printf("%s ", it2->get_state().c_str());
		}
		printf("\n");
	}

}

bool InterpolantSolver::all_terminations_are_rejected(vector<vector<string> > rejecting_information){

	for( vector<vector<string> >::iterator it = rejecting_information.begin(); it != rejecting_information.end(); it++ ){
		vector<string> row = *it;
		bool one_or_more_columns_terminate = 0;
		for( vector<string>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
			if(*it2 == options->cmd_option_str("target_node") + "_0") one_or_more_columns_terminate = 1;
		}

		if(!one_or_more_columns_terminate) return false;
	}
	

	return true;
}

vector<string> InterpolantSolver::rejecting_automaton_states( vector<Automaton> vector_automatons ){

	vector<string> ret;

	if(vector_automatons[0].get_state() != options->cmd_option_str("target_node")) return ret;

	for ( unsigned int i = 1; i < vector_automatons.size(); i++) {
		ret.push_back(vector_automatons[i].get_state());
	}

	return ret;

}

string InterpolantSolver::condition_of(string content, bool invert){


	printf("\e[32m InterpolantSolver::condition_of \e[0m %s %d\n", content.c_str(), invert);

	string ret;

	if(content.substr(0,6) == "(not (" )
		return condition_of(content.substr(6), 1);

        if     (content.substr(1,2) == "<="   ) ret = "<=";
        else if(content.substr(1,2) == ">="   ) ret = "<=";
        else if(content.substr(1,1) == "<"    ) ret = "<";
        else if(content.substr(1,1) == "<"    ) ret = ">=";
        else if(content.substr(1,1) == "="    ) ret = "=";
        else if(content             == "true" ) ret = "true";
	else{
		printf("content %s\n", content.c_str());
		assert(0 && "Unknown condition"); 
	}

	if(invert) ret = negate_polarity(ret);

	return ret;

}

string InterpolantSolver::negate_polarity(string predicate){

	if( predicate == "="  ) return "#"; 
	if( predicate == ">"  ) return "<=";
	if( predicate == ">=" ) return "<";
	if( predicate == "<"  ) return ">=";
	if( predicate == "<=" ) return ">";
	if( predicate == "#"  ) return "=";
	printf("predicate %s\n", predicate.c_str());
	if(isdriver)assert(0 && "Unknown Operation");
}

string InterpolantSolver::bb_name(string name, bool side_effects){
	if(side_effects){
		sequential_identifier_bbs[name]++;
		return name + "_" + itos(sequential_identifier_bbs[name]-1);
	} else {
		return name + "_" + itos(sequential_identifier_bbs[name]-1);
	}
}

void InterpolantSolver::print_possible_combinations(set<vector<string> > result ){

	printf("\e[32m Possible combinations \e[0m\n");
	for( set<vector<string> >::iterator it = result.begin(); it != result.end(); it++ ){
		vector<string> ittr = *it;
		for( vector<string>::iterator it2 = ittr.begin(); it2 != ittr.end(); it2++ ){
			printf("%s ", it2->c_str());
		}
		printf("\n");
	}
	printf("\e[32m === \e[0m\n");
}

void InterpolantSolver::print_possible_tansitions(vector<set<string> > possible_transitions){

	printf("\e[32m Possible transitions\e[0m\n");
	int n = 0;
	for( vector<set<string> >::iterator it = possible_transitions.begin(); it != possible_transitions.end(); it++ ){
		n++;
		set<string> column = *it;
		for( set<string>::iterator it2 = column.begin(); it2 != column.end(); it2++ ){
			string cell = *it2;
			printf("%d %s\n", n, cell.c_str());
		}
	}
	printf("\e[32m === \e[0m\n");
	
}

void print_states(vector<vector<Automaton> > matrix_automaton){

	printf("\e[32m States \e[0m\n");

	for( vector<vector<Automaton> >::iterator it = matrix_automaton.begin(); it != matrix_automaton.end(); it++ ){
		vector<Automaton> row = *it;

		for( vector<Automaton>::iterator it2 = row.begin(); it2 != row.end(); it2++ ){
			string state = it2->get_state();
			printf("%s ", state.c_str());
		}
		printf("\n");
		
	}
	printf("\e[32m === \e[0m\n");
	

}

//////

InterpolantSolver::~InterpolantSolver(){
	
}

bool InterpolantSolver::solvable_problem(){
	if(is_in_interpolant) return false;

	z3solver->get_context(this);
	bool ret = z3solver->solvable_problem();
	get_context_back(z3solver);
	return ret;
}

void InterpolantSolver::sym_store(string src, string addr){
	z3solver->get_context(this);
	z3solver->sym_store(src, addr);
	get_context_back(z3solver);
}

void InterpolantSolver::sym_load(string dst, string idx_content){
	z3solver->get_context(this);
	z3solver->sym_load(dst, idx_content);
	get_context_back(z3solver);
}

void InterpolantSolver::push_condition_static_var(string cond, bool invert){
	z3solver->get_context(this);
	z3solver->push_condition_static_var(cond, invert);
	get_context_back(z3solver);
}

void InterpolantSolver::load_state(){

	stack_of_conditions       = stack_of_conditions_bak;
	sequential_identifier_bbs = sequential_identifier_bbs_bak;

	z3solver->get_context(this);
	z3solver->load_state();
	get_context_back(z3solver);
}

void InterpolantSolver::save_state(){

	stack_of_conditions_bak       = stack_of_conditions;
	sequential_identifier_bbs_bak = sequential_identifier_bbs;

	z3solver->get_context(this);
	z3solver->save_state();
	get_context_back(z3solver);
}

void InterpolantSolver::pointer_instruction(string dst, string offset_tree, vector<string> indexes, string base){
	z3solver->get_context(this);
	z3solver->pointer_instruction(dst, offset_tree,  indexes, base);
	get_context_back(z3solver);
}

string InterpolantSolver::debug_content( string name ){
	z3solver->get_context(this);
	string ret = z3solver->debug_content( name );
	get_context_back(z3solver);
	return ret;
}

int InterpolantSolver::show_problem(){
	z3solver->get_context(this);
	int ret = z3solver->show_problem();
	get_context_back(z3solver);
	return ret;
}

void InterpolantSolver::set_offset_tree( string varname, string tree ){
	z3solver->get_context(this);
	z3solver->set_offset_tree( varname, tree );
	get_context_back(z3solver);
}

void InterpolantSolver::cast_instruction_content(string src, string dst, string type_src, string type_dst, string sext){

	z3solver->get_context(this);
	z3solver->cast_instruction(src, dst, type_src, type_dst, sext);
	get_context_back(z3solver);
}

void InterpolantSolver::bool_to_int8(string src, string dst){
	z3solver->get_context(this);
	z3solver->bool_to_int8(src, dst);
	get_context_back(z3solver);
}

void InterpolantSolver::bool_to_int32(string src, string dst){
	z3solver->get_context(this);
	z3solver->bool_to_int32(src, dst);
	get_context_back(z3solver);
}

string InterpolantSolver::internal_condition(string condition){
	z3solver->get_context(this);
	string ret = z3solver->internal_condition(condition);
	get_context_back(z3solver);
	return ret;

}

string InterpolantSolver::internal_representation(int in, string type){

	z3solver->get_context(this);
	string ret = z3solver->internal_representation(in, type);
	get_context_back(z3solver);
	return ret;


}

map<set<pair<string, int> > , int > InterpolantSolver::get_idx_val(string base,string idx_content, vector<string> indexes, int first_address, int last_address){
	z3solver->get_context(this);
	map<set<pair<string, int> > , int > ret = z3solver->get_idx_val(base,idx_content,  indexes, first_address, last_address);
	get_context_back(z3solver);
	return ret;

}

void InterpolantSolver::clear_variable(string var){
	z3solver->get_context(this);
	z3solver->clear_variable(var);
	get_context_back(z3solver);
}

void InterpolantSolver::save_first_content(string var, string dst){
	z3solver->get_context(this);
	z3solver->save_first_content(var, dst);
	get_context_back(z3solver);
}

void InterpolantSolver::variable_store(string src,string idx_content, int first_address, int last_address ){
	z3solver->get_context(this);
	z3solver->variable_store(src,idx_content, first_address, last_address );
	get_context_back(z3solver);
}

string InterpolantSolver::canonical_representation(string in){
	z3solver->get_context(this);
	string ret = z3solver->canonical_representation(in);
	get_context_back(z3solver);
	return ret;
}

string InterpolantSolver::content_smt(string name){
	z3solver->get_context(this);
	string ret = z3solver->content_smt(name);
	get_context_back(z3solver);
	return ret;
}

void InterpolantSolver::propagate_unary_extra(string src, string dst, bool forcedfree){
	z3solver->get_context(this);
	z3solver->propagate_unary_extra(src, dst, forcedfree);
	get_context_back(z3solver);
}

void InterpolantSolver::propagate_binary_extra(string op1, string op2, string dst){
	z3solver->get_context(this);
	z3solver->propagate_binary_extra(op1, op2, dst);
	get_context_back(z3solver);
}

void InterpolantSolver::add_neq_zero(string var){
	z3solver->add_neq_zero(var);
}

void InterpolantSolver::add_eq_zero(string var){
	z3solver->add_eq_zero(var);
}

void InterpolantSolver::dump_conditions(stringstream& sstream){
	assert(0 && "Not Implemented");
}

void InterpolantSolver::dump_model(){
	assert(0 && "Not implemented");
}

void InterpolantSolver::dump_check_sat(FILE* file){
	fprintf(file, "(check-sat)\n");
}

map<set<pair <string, int> >, int> InterpolantSolver::get_map_idx_val(string name){
	assert(0 && "Not Implemented");
}


void InterpolantSolver::add_eq_set(set<pair <string, int> > set_idx_val){
	assert(0 && "Not Implemented");
}




void InterpolantSolver::set_content(string name, string value){

	assert(0 && "not implemented");

}


string InterpolantSolver::eval(string expression){
	assert(0 && "Not Implemented");
}


void InterpolantSolver::add_bt(string var, string val){

	assert(0 && "Not Implemented");

}

void InterpolantSolver::add_lt(string var, string val){

	assert(0 && "Not Implemented");

}

pair<int, int> InterpolantSolver::get_range(string name){

	assert(0 && "Not Implemented");

}


bool InterpolantSolver::empty_assertions(){

	assert(0 && "Not Implemented");

}


void InterpolantSolver::add_smt(string smt){

	assert(0 && "Not Implemented");

}
