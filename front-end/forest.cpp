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

void show_help() {
    int const WIDTH = 30;

    std::cout << "Usage: forest [options]" << std::endl;
    std::cout << "Options:" << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-version"                  << "Print version info." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-help"                     << "Displays this information." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-verbose"                  << "Displays a lot of debug information." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-make_bc"                  << "Generates bc with instrumentation and isolated function." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-clean_tables"             << "Removes and creates database tables." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-final"                    << "Generates final executable code." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-compare_bc"               << "Opens meld comparing the original and instrumented LLVM IR." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-compare_libs"             << "Compares raw bc with changed-stdlibs." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-view_bc"                  << "Shows bc of the code." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-dfg"                      << "Shows dfg of the code." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-dfg2"                     << "Shows dfg of instrumented code." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-run"                      << "Run generated executable." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-test"                     << "Run and check results." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_results"             << "Lists the results of a previous forest run." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_argvs"               << "Show generated testcases in argv form." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_test_vectors"        << "Show generated testvectors." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-test_vectors"             << "Transforms data in the database to test_vector format." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_coverage"            << "Shows coverage obtained with current test_vectors." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-clean"                    << "Creates and cleans temporal folder." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_result"               << "Copies result to gold_result." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-vim"                      << "Shows debug information in vim." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_model"                << "Gets a model to be used in repl." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_model_fn"             << "Gets a model of a function." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_model_modelfinder"    << "Gets a model to be used with the modelfinder tool." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_static_heuristic"     << "Generates heuristics to guide the search." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-valgrind"                 << "Tests the output with valgrind ." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-list_external_functions"  << "Lists the functions that are not implemented." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-lbc"                      << "Get the bc linked with standard libraries." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_timer"               << "Draws a graph with timer." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_exceptions"          << "Shows possible exceptions in the program under test." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-show_interpolants"        << "Shows interpolants." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-svcomp"                   << "svcomp competition." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-goanna_fpr"               << "Use forest to check for false positives in goanna." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-get_concurrent_functions" << "Get functions that can be executed concurrently." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-commutativity"            << "Run commutativity_testing." << std::endl;
    std::cout <<  std::setw(WIDTH) << std::left <<  "-compare_isolate"          << "Isolate function and compare with original." << std::endl;

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
	needs("get_result", "test");
	needs("vim", "final");
	needs("vim", "clean_tables");
	needs("valgrind", "final");
	needs("svcomp", "clean");
	needs("svcomp", "heuristic");
	needs("svcomp", "final");
	needs("svcomp", "clean_tables");
	needs("goanna_fpr", "svcomp");


	disables("compare_bc", "test");
	disables("compare_isolate", "test");
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
	disables("compare_bc", "test");
	disables("compare_bc", "check_coverage");
	disables("compare_measure_bc", "test");
	disables("compare_secuencialize", "test");
	disables("test_vectors", "test");
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
	//cmd_option_bool("location_names")
	//cmd_option_bool("recursive")
	//cmd_option_bool("heuristic_recursive_depth")
	//cmd_option_bool("max_heuristic_paths")
	//cmd_option_bool("show_heuristic_graph")
	//cmd_option_bool("visualize_coverage"))
	//cmd_option_bool("random_branching"))
	//cmd_option_bool("svcomp_only_output"))
	if(cmd_option_bool("version")) show_version_and_exit();                     // print version info
    if(cmd_option_bool("help")) show_help();                                    // Show all possible command line arguments for forest
	if(cmd_option_bool("make_bc")) make_bc();                                   // generates bc with instrumentation and isolated function
	if(cmd_option_bool("clean_tables")) clean_tables();                         // removes and creates database tables
	if(cmd_option_bool("final")) final();                                       // generates final executable code
	if(cmd_option_bool("compare_bc")) compare_bc();                             // compares raw bc with instrumented one
	if(cmd_option_bool("compare_libs")) compare_libs();                         // compares raw bc with changed-stdlibs
	if(cmd_option_bool("view_bc")) view_bc();                                   // shows bc of the code
	if(cmd_option_bool("dfg")) view_dfg();                                      // shows dfg of the code
	if(cmd_option_bool("dfg2")) view_dfg_2();                                   // shows dfg of instrumented code
	if(cmd_option_bool("run")) run();                                           // run generated executable
	if(cmd_option_bool("test")) test();                                         // run and check results
	if(cmd_option_bool("show_results")) show_results();                         // show generated testcases
	if(cmd_option_bool("show_argvs")) show_argvs();                             // show generated testcases in argv form
	if(cmd_option_bool("show_test_vectors")) show_test_vectors();               // show generated testvectors
	if(cmd_option_bool("test_vectors")) minimal_test_vectors_to_db();           // transforms data in the database to test_vector format
	if(cmd_option_bool("show_coverage")) show_coverage();                       // shows coverage obtained with current test_vectors
	if(cmd_option_bool("clean")) clean();                                       // creates and cleans temporal folder
	if(cmd_option_bool("get_result")) get_result();                             // copies result to gold_result
	if(cmd_option_bool("vim")) vim();                                           // shows debug information in vim
	if(cmd_option_bool("get_model")) get_model();                               // gets a model to be used in repl
	if(cmd_option_bool("get_model_fn")) get_model_fn();                         // gets a model of a function
	if(cmd_option_bool("get_model_modelfinder")) get_model_modelfinder();       // gets a model to be used with the modelfinder tool
	if(cmd_option_bool("get_static_heuristic")) get_static_heuristic();         // generates heuristics to guide the search
	if(cmd_option_bool("valgrind")) valgrind();                                 // tests the output with valgrind 
	if(cmd_option_bool("list_external_functions")) list_external_functions();   // lists the functions that are not implemented
	if(cmd_option_bool("lbc")) linked_bc();                                     // get the bc linked with standard libraries
	if(cmd_option_bool("show_timer")) show_timer();                             // draws a graph with timer
	if(cmd_option_bool("show_exceptions")) show_exceptions();                   // Shows possible exceptions in the program under test
	if(cmd_option_bool("show_interpolants")) show_interpolants();               // Shows interpolants
	if(cmd_option_bool("svcomp")) svcomp();                                     // svcomp competition
	if(cmd_option_bool("goanna_fpr")) goanna_fpr();                             // Use forest to check for false positives in goanna
	if(cmd_option_bool("get_concurrent_functions")) get_concurrent_functions(); // Get functions that can be executed concurrently
	if(cmd_option_bool("commutativity")) commutativity_testing();               // Run commutativity_testing
	if(cmd_option_bool("compare_isolate")) compare_isolate();                   // Isolate function and compare with original
	return 0;

}

