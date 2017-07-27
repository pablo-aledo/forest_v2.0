/*
 * =====================================================================================
 * /
 * |     Filename:  forest.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/21/2013 12:35:23 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *      ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include "forest.h"


#define SIZE_STR 512

#define debug false

using namespace std;





// typedefs



// Pass functions

void show_version_and_exit(){
	printf("svc_16_20151108\n");
	exit(0);
}

int main(int argc, const char *argv[]) {


	load_default_options();
	set_current_path();
	create_tmp_path();

	if( argc >= 2 && argv[1][0] != '-' ){
		set_project_path( string(argv[1]) );
		load_file_options( string(argv[1]) );
	} else {
		set_project_path( get_current_path() + "/config.xml" );
		load_file_options();
	}

	load_cmd_options(argc, argv);
	options_to_file();

	needs("test", "run");
	needs("final", "make_bc");
	needs("run", "final");
	needs("run", "clean_tables");
	needs("make_bc", "clean");
	needs("check_coverage", "measure_coverage");
	needs("compare_klee", "run");
	needs("compare_klee", "klee");
	needs("get_result", "test");
	needs("vim", "final");
	needs("vim", "clean_tables");
	needs("valgrind", "final");
	needs("svcomp", "clean");
	needs("svcomp", "heuristic");
	needs("svcomp", "final");
	needs("svcomp", "clean_tables");
	needs("goanna_fpr", "svcomp");
	needs("compare_xml", "generate_uppaal_model");
	//needs("klee_coverage", "measure_coverage");
	//needs("klee_coverage", "klee");


	disables("compare_bc", "test");
	disables("get_concurrent_functions", "test");
	disables("compare_libs", "test");
	disables("make_bc", "test");
	disables("view_bc", "test");
	disables("view_bc", "check_coverage");
	disables("dfg", "test");
	disables("dfg", "svcomp");
	disables("dfg", "check_coverage");
	disables("dfg2", "test");
	disables("dfg2", "check_coverage");
	disables("run", "test");
	disables("vim", "test");
	disables("valgrind", "test");
	disables("show_results", "test");
	disables("show_results", "check_coverage");
	disables("show_test_vectors", "test");
	disables("show_test_vectors", "check_coverage");
	disables("show_argvs", "test");
	disables("show_argvs", "check_coverage");
	disables("klee", "test");
	disables("klee", "compare_klee");
	disables("klee", "check_coverage");
	disables("compare_bc", "test");
	disables("compare_bc", "check_coverage");
	disables("compare_measure_bc", "test");
	disables("compare_secuencialize", "test");
	disables("compare_klee", "test");
	disables("compare_klee", "check_coverage");
	disables("test_vectors", "test");
	disables("test_vectors", "compare_klee");
	disables("get_model", "test");
	disables("get_model_fn", "test");
	disables("get_model_modelfinder", "test");
	disables("get_static_heuristic", "test");
	disables("get_static_heuristic", "check_coverage");
	disables("list_external_functions", "test");
	disables("list_external_functions", "check_coverage");
	disables("lbc", "test");
	disables("lbc", "check_coverage");
	disables("measure_coverage", "test");
	disables("tests_from_klee", "test");
	disables("tests_from_klee", "check_coverage");
	disables("show_coverage", "test");
	disables("show_coverage", "check_coverage");
	disables("show_timer", "test");
	disables("show_timer", "check_coverage");
	disables("show_exceptions", "test");
	disables("show_exceptions", "check_coverage");
	disables("show_interpolants", "test");
	disables("show_interpolants", "check_coverage");


	expand_options();


	//cmd_option_bool("verbose")
	//cmd_option_bool("see_each_problem")
	//cmd_option_bool("seq_name")
	//cmd_option_bool("with_libs")
	//cmd_option_bool("cyclotonic")
	//cmd_option_bool("unconstrained")
	//cmd_option_bool("dfg_function")
	//cmd_option_bool("show_only_constraints")
	//cmd_option_bool("show_bdd")
	//cmd_option_bool("bdd_permutation")
	//cmd_option_bool("solver")
	//cmd_option_bool("svcomp")
	//cmd_option_bool("bigsize")
	//cmd_option_bool("show_frontier")
	//cmd_option_bool("stop_in_frontier")
	//cmd_option_bool("max_time_min")
	//cmd_option_bool("generate_model")
	//cmd_option_bool("fork_on_array")
	//cmd_option_bool("uppaal_simplify")
	//cmd_option_bool("no_uppaal_names")
	//cmd_option_bool("no_uppaal_simplify")
	//cmd_option_bool("location_names")
	//cmd_option_bool("no_uppaal_if")
	//cmd_option_bool("recursive")
	//cmd_option_bool("heuristic_recursive_depth")
	//cmd_option_bool("max_heuristic_paths")
	//cmd_option_bool("show_heuristic_graph")
	//cmd_option_bool("visualize_coverage"))
	//cmd_option_bool("random_branching"))
	//cmd_option_bool("svcomp_only_output"))
	if(cmd_option_bool("version")) show_version_and_exit();                     // print version info
	if(cmd_option_bool("make_bc")) make_bc();                                   // generates bc with instrumentation and isolated function
	if(cmd_option_bool("clean_tables")) clean_tables();                         // removes and creates database tables
	if(cmd_option_bool("final")) final();                                       // generates final executable code
	if(cmd_option_bool("compare_bc")) compare_bc();                             // compares raw bc with instrumented one
	if(cmd_option_bool("compare_measure_bc")) compare_measure_bc();             // compares raw bc with measurement one
	if(cmd_option_bool("compare_libs")) compare_libs();                         // compares raw bc with changed-stdlibs
	if(cmd_option_bool("view_bc")) view_bc();                                   // shows bc of the code
	if(cmd_option_bool("dfg")) view_dfg();                                      // shows dfg of the code
	if(cmd_option_bool("dfg2")) view_dfg_2();                                   // shows dfg of instrumented code
	if(cmd_option_bool("run")) run();                                           // run generated executable
	if(cmd_option_bool("test")) test();                                         // run and check results
	if(cmd_option_bool("show_results")) show_results();                         // show generated testcases
	if(cmd_option_bool("show_argvs")) show_argvs();                             // show generated testcases in argv form
	if(cmd_option_bool("show_test_vectors")) show_test_vectors();               // show generated testvectors
	if(cmd_option_bool("measure_coverage")) measure_coverage();                 // measure coverage obtained with current test_vectors
	if(cmd_option_bool("test_vectors")) minimal_test_vectors_to_db();           // transforms data in the database to test_vector format
	if(cmd_option_bool("show_coverage")) show_coverage();                       // shows coverage obtained with current test_vectors
	if(cmd_option_bool("random_testing")) random_testing();                     // fuzzes free variables
	if(cmd_option_bool("klee")) do_klee();                                      // tests the program with klee
	if(cmd_option_bool("clean")) clean();                                       // creates and cleans temporal folder
	if(cmd_option_bool("compare_klee")) compare_klee();                         // compares times and paths for klee and forest
	if(cmd_option_bool("get_result")) get_result();                             // copies result to gold_result
	if(cmd_option_bool("vim")) vim();                                           // shows debug information in vim
	if(cmd_option_bool("check_coverage")) check_coverage();                     // checks if coverage is as good as expected
	if(cmd_option_bool("get_model")) get_model();                               // gets a model to be used in repl
	if(cmd_option_bool("get_model_fn")) get_model_fn();                         // gets a model of a function
	if(cmd_option_bool("get_model_modelfinder")) get_model_modelfinder();       // gets a model to be used with the modelfinder tool
	if(cmd_option_bool("get_static_heuristic")) get_static_heuristic();         // generates heuristics to guide the search
	if(cmd_option_bool("valgrind")) valgrind();                                 // tests the output with valgrind 
	if(cmd_option_bool("list_external_functions")) list_external_functions();   // lists the functions that are not implemented
	if(cmd_option_bool("lbc")) linked_bc();                                     // get the bc linked with standard libraries
	if(cmd_option_bool("tests_from_klee")) tests_from_klee();                   // get the test_vectors from klee output
	if(cmd_option_bool("klee_coverage")) klee_coverage();                       // get the coverage of tests generaged by klee
	if(cmd_option_bool("show_timer")) show_timer();                             // draws a graph with timer
	if(cmd_option_bool("show_exceptions")) show_exceptions();                   // Shows possible exceptions in the program under test
	if(cmd_option_bool("show_interpolants")) show_interpolants();               // Shows interpolants
	if(cmd_option_bool("svcomp")) svcomp();                                     // svcomp competition
	if(cmd_option_bool("generate_uppaal_model")) generate_uppaal_model();       // uppaal model
	if(cmd_option_bool("compare_xml")) compare_xml();                           // check uppaal model with Kactus dependency xml model
	if(cmd_option_bool("goanna_fpr")) goanna_fpr();                             // Use forest to check for false positives in goanna
	if(cmd_option_bool("get_concurrent_functions")) get_concurrent_functions(); // Get functions that can be executed concurrently

	return 0;

}

