/*
 * =====================================================================================
 * /
 * |     Filename:  bc_handling.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  11/03/2014 04:13:50 PM
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

#include "bc_handling.h"

#define SIZE_STR 1024

void make_bc(){

	start_pass("make_bc");

	options_to_file();

	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	if(cmd_option_str("seed_function") != ""){
		cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -isolate_function < file.bc > file-2.bc";
		systm(cmd.str().c_str());
		cmd.str("");
		cmd << "mv file-2.bc file.bc";
		systm(cmd.str().c_str());
	}

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	end_pass("make_bc");

}

void compare_bc(){

	start_pass("compare_bc");


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Disassembly
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());


	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Disassembly
	cmd.str("");
	cmd << "llvm-dis < file-3.bc > salida2.txt";
	systm(cmd.str().c_str());


	// Comparison
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());


	end_pass("compare_bc");

}

void compare_measure_bc(){


	string base_path = cmd_option_str("base_path");
	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_fillnames < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Disassembly
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());


	// Second optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestMeasure.so -meas_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());

	// Disassembly
	cmd.str("");
	cmd << "llvm-dis < file-3.bc > salida2.txt";
	systm(cmd.str().c_str());


	// Comparison
	cmd.str("");
	cmd << "meld salida1.txt salida2.txt";
	systm(cmd.str().c_str());



}

void view_bc(){

	start_pass("view_bc");

	string llvm_path = cmd_option_str("llvm_path");
	stringstream cmd;

	make_initial_bc();

	// First optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Disassembly
	cmd.str("");
	cmd << "llvm-dis < file-2.bc > salida1.txt";
	systm(cmd.str().c_str());

	// Visualize
	cmd.str("");
	cmd << "gedit salida1.txt &";
	systm(cmd.str().c_str());

	end_pass("view_bc");

}

void final(){

	start_pass("final");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	stringstream cmd;

	if(cmd_option_bool("link_bc")){
		// Link
		cmd.str("");
		cmd << "llvm-link -o=" << tmp_file("final.bc") << " " << base_path << "/lib/forest.a file-3.bc";
		systm(cmd.str().c_str());

		// Optimization
		cmd.str("");
		cmd << "opt -std-compile-opts < final.bc > final-2.bc;";
		cmd << "mv final-2.bc final.bc";
		systm(cmd.str().c_str());

		// From .bc to .s
		cmd.str("");
		cmd << "llc final.bc -o final.s";
		systm(cmd.str().c_str());

		// From .s to .o
		cmd.str("");
		cmd << "gcc -c final.s -o final.o";
		systm(cmd.str().c_str());

		// link
		cmd.str("");
		cmd << "g++ final.o -lpthread -ldl -lrt -o " << output_file;
		systm(cmd.str().c_str());
	} else {
		// From .bc to .s
		cmd.str("");
		cmd << "llc file-3.bc -o file-3.s";
		systm(cmd.str().c_str());

		// From .s to .o
		cmd.str("");
		cmd << "gcc -c file-3.s -o file-3.o";
		systm(cmd.str().c_str());

		// link
		cmd.str("");
		cmd << "g++ file-3.o " << base_path << "/lib/forest.a" << " -lpthread -ldl -lrt -o " << output_file;
		systm(cmd.str().c_str());
	}


	end_pass("final");

}


void test(){

	start_pass("test");

	string explanation = cmd_option_str("explanation") + " ";

	while( explanation.length() < 55 )
		explanation = explanation + ".";

	printf("* Testing %s", explanation.c_str() );

	stringstream cmd;

	// Show database results
	cmd.str("");
	cmd << "echo '.mode columns\\n.width 25 5 5\\n.headers on\\nselect name_hint,value, problem_id from results where is_free;'";
	cmd << " | sqlite3 " << tmp_file("database.db") << " ";
	cmd << "> " << tmp_file("results");
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "cd " << tmp_dir() << ";";
	cmd << "diff results " << prj_file("gold_result_" + cmd_option_str("solver")) << " > /dev/null";
	int result = system(cmd.str().c_str());

	if( result )
		printf("\e[31m Failed :( \e[0m\n");
	else
		printf("\e[32m Passed :) \e[0m\n");

	end_pass("test");
}

void view_dfg(){


	stringstream cmd;


	make_initial_bc();





	// DOT optimization pass
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "cd " << tmp_dir() << "; ";
	command << "opt -dot-cfg < file.bc 2>&1 | grep Writing";
	
	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	
	vector<string> gen_dfgs;

	if(cmd_option_str("dfg_function") == ""){
		for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
			vector<string> tokens = tokenize(*it, "'");
			gen_dfgs.push_back(tokens[1]);
		}
	} else {
		gen_dfgs.push_back("cfg." + cmd_option_str("dfg_function") + ".dot");
	}
	
	

	for( vector<string>::iterator it = gen_dfgs.begin(); it != gen_dfgs.end(); it++ ){

		// From .dot to .png
		cmd.str("");
		cmd << "dot -T png " << *it << " > " << *it << ".png";
		systm(cmd.str().c_str());

		// show png
		cmd.str("");
		cmd << "eog " << *it << ".png &";
		systm(cmd.str().c_str());
		
	}

}

void view_dfg_2(){


	stringstream cmd;


	make_initial_bc();

	string llvm_path = cmd_option_str("llvm_path");

	// First Optimization pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file.bc > file-2.bc";
	systm(cmd.str().c_str());

	// Second optimizatio pass
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_all < file-2.bc > file-3.bc";
	systm(cmd.str().c_str());



	// Dot optimizatio pass
	FILE *fp;
	stringstream command;
	char ret[SIZE_STR];
	vector<string> ret_vector;
	
	command << "cd " << tmp_dir() << "; ";
	command << "opt -dot-cfg < file-3.bc 2>&1 | grep Writing";
	
	fp = popen(command.str().c_str(), "r");
	
	while (fgets(ret,SIZE_STR, fp) != NULL)
		ret_vector.push_back(ret);
	
	pclose(fp);
	
	vector<string> gen_dfgs;

	for( vector<string>::iterator it = ret_vector.begin(); it != ret_vector.end(); it++ ){
		vector<string> tokens = tokenize(*it, "'");
		gen_dfgs.push_back(tokens[1]);
	}
	
	

	for( vector<string>::iterator it = gen_dfgs.begin(); it != gen_dfgs.end(); it++ ){

		// from .dot to .png
		cmd.str("");
		cmd << "dot -T png " << *it << " > " << *it << ".png";
		systm(cmd.str().c_str());

		// show the png
		cmd.str("");
		cmd << "eog " << *it << ".png &";
		systm(cmd.str().c_str());
		
	}

}

void vim(){

	start_pass("vim");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	dump_forced_free_vars();
	dump_forced_free_hints();

	stringstream cmd;

	set_option("verbose", "true");
	options_to_file();

	// Execute resulting file
	cmd.str("");
	cmd << "./" << output_file << " > output;";
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "gvim +AnsiEsc " << "output;";
	systm(cmd.str().c_str());

	end_pass("vim");

}

void valgrind(){

	start_pass("valgrind");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	dump_forced_free_vars();
	dump_forced_free_hints();

	stringstream cmd;

	set_option("verbose", "true");
	options_to_file();

	// Ejecute resulting file
	cmd.str("");
	cmd << "valgrind ./" << output_file << " 2>&1 | tee output";
	systm(cmd.str().c_str());


	cmd.str("");
	cmd << "gvim +AnsiEsc " << "output;";
	systm(cmd.str().c_str());

	end_pass("valgrind");

}

void clean(){

	start_pass("clean");

	stringstream cmd;

	// Creates and cleans temporary folder
	cmd.str("");
	cmd << "rm -rf " << tmp_dir() << ";";
	cmd << "mkdir -p " << tmp_dir() << ";";
	systm(cmd.str().c_str());

	end_pass("clean");

}

void get_result(){
	start_pass("get_result");

	stringstream cmd;
	cmd << "cp " << tmp_file("results") << " " << prj_file("gold_result_" + cmd_option_str("solver"));
	systm(cmd.str());

	end_pass("get_result");
}

int get_last_include_line(vector<string> lines){
	//printf("get_last_include_line\n");
	int ret = 0;
	for ( unsigned int i = 0; i < lines.size();) {
		//printf("i %d\n", i);
		if(lines[i].find("extern") != string::npos && \
		   lines[i].find("VERIFIER") == string::npos ){
			while( i < lines.size()-1 && lines[i] != "" ){
				//printf("I %d\n", i);
				i++;
				ret = i;
			}
		}
		i++;
	}
	
	//printf("ret %d\n", ret);
	//exit(0);
	return ret;
}

void make_initial_bc(){

	stringstream cmd;

	string llvm_path = cmd_option_str("llvm_path");
	string base_path = cmd_option_str("base_path");

	if( is_bc(cmd_option_string_vector("file")[0]) ){
		// Copies BC to temporary folder
		cmd.str("");
		cmd << "cp ";
		cmd << prj_file(cmd_option_str("file"));
		cmd << " " << tmp_file("file.bc");
		systm(cmd.str().c_str());
	} else if (is_bs(cmd_option_string_vector("file")[0])){
		cmd.str("");
		cmd << "llvm-as ";
		cmd << prj_file(cmd_option_str("file"));
		cmd << " -o " << tmp_file("file.bc");
		systm(cmd.str().c_str());
	} else {
		// Joins all c files in one
		cmd.str("");
		cmd << "cat ";
		vector<string> files = cmd_option_string_vector("file");
		for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
			cmd << prj_file(*it) << " ";
		}
		if(cmd_option_str("c_standard") == "C"){
			cmd << "> " << tmp_file("file.c") << ";";
		} else {
			cmd << "> " << tmp_file("file.cpp");
		}
		systm(cmd.str().c_str());


		if(cmd_option_bool("sequentialize")){


			if(false && cmd_option_bool("svcomp")){
				//ifstream input(tmp_file("file.c").c_str());
				//string line;
				vector<string> lines;

				vector<string> outlines;

				//while( getline( input, line ) ) {
					//lines.push_back(line);
				//}
				//exit(0);

				FILE *file1 = fopen ( tmp_file("file.c").c_str(), "r" );
				char line [1024]; /* or other suitable maximum line size */
				
				while ( fgets ( line, sizeof(line), file1 ) != NULL ){
					line[strlen(line)-1] = 0;
					lines.push_back(string(line));
				}
				fclose ( file1 );

				int n = get_last_include_line(lines);
				if(n>10){
					n = n+1; 
				} else {
					n = 0;
				}

				for ( unsigned int i = 0; i < n; i++) {
					lines.erase(lines.begin());
				}


				for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
					outlines.push_back(*it);
				}


				//printf("outlines.size() %lu\n", outlines.size());
				FILE* file = fopen(tmp_file("file.c").c_str(), "w");
				for( vector<string>::iterator it = outlines.begin(); it != outlines.end(); it++ ){
					fprintf(file, "%s\n", it->c_str());
				}
				fclose(file);

				//exit(0);


			}

			cmd.str("");
			cmd << "cp " << tmp_file("file.c") << " " << tmp_file("file.i");
			systm(cmd.str().c_str());


			// Back-ends
			// blitz cbmc esbmc llbmc
			// cpachecker satabs
			// klee cbmc

			cmd.str("");
			cmd << "cd " << cmd_option_str("cseq_path") << ";";
			cmd << "./cseq.py --backend cpachecker -i " << tmp_file("file.i") << " > " << tmp_file("file_seq.c");
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "cp " << tmp_file("file_seq.c") << " " << tmp_file("file.c");
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "sed -i ";
			//cmd << "-e 's/size_t/int/g' ";
			cmd << "-e 's/#include.*//g' ";
			cmd << "-e 's/__CSEQ_atomic_.*//g' ";
			cmd << tmp_file("file.c");
			systm(cmd.str().c_str());

		}


		if(cmd_option_str("c_standard") == "C"){
			cmd.str("");
			cmd << "sed -i 's/#include .assert.h./#define LARGE_INT 1000000/g' " << tmp_file("file.c");
			systm(cmd.str().c_str());


			cmd.str("");
			cmd << "sed -i 's/size_t/int/g' " << tmp_file("file.c");
			systm(cmd.str().c_str());
		}



		if(cmd_option_bool("svcomp") && !cmd_option_bool("sequentialize")){
			ifstream input(tmp_file("file.c").c_str());
			string line;
			vector<string> lines;
			vector<string> outlines;

			while( getline( input, line ) ) {
				lines.push_back(line);
			}


			int n = get_last_include_line(lines);
			if(n>10){
				n = n+1; 
			} else {
				n = 0;
			}

			for ( unsigned int i = 0; i < n; i++) {
				lines.erase(lines.begin());
			}

			for( vector<string>::iterator it = lines.begin(); it != lines.end(); it++ ){
				if(it->find("stdlib.h") != string::npos){
					outlines.push_back("void* fr_malloc(int size);");
					outlines.push_back("void* fr_alloca(int size);");
					outlines.push_back("void  fr_free(void* pointer);");
				} else {
					outlines.push_back(*it);
				}
			}


			FILE* file = fopen(tmp_file("file.c").c_str(), "w");
			for( vector<string>::iterator it = outlines.begin(); it != outlines.end(); it++ ){
				fprintf(file, "%s\n", it->c_str());
			}
			fclose(file);

			//exit(0);
			

			
		}

		

		if(cmd_option_bool("rm_include")){
			cmd.str("");
			cmd << "sed -i 's/#include.*//g' " << tmp_file("file.c*");
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "sed -i '1i#define NULL 0' " << tmp_file("file.c*");
			systm(cmd.str().c_str());


			cmd.str(""); cmd << "sed -i '1ichar* malloc(int a);' " << tmp_file("file.c*"); systm(cmd.str().c_str());
			cmd.str(""); cmd << "sed -i '1ichar* alloca(int a);' " << tmp_file("file.c*"); systm(cmd.str().c_str());
			cmd.str(""); cmd << "sed -i '1ivoid  free(void* a);' " << tmp_file("file.c*"); systm(cmd.str().c_str());


		}

		if(cmd_option_bool("workaround_subst")){
			cmd.str("");
			cmd << "sed -i ";
			cmd << "-e s/timer/timer_aux/g ";
			cmd << "-e 's/__attribute__ ((__noreturn__))//g' ";
			cmd << tmp_file("file.c");
			systm(cmd.str());
		}


		string cflags;
		if(cmd_option_bool("with_libs"))
			cflags = "-I" + base_path + "/stdlibs/include/";

		string bigsize_str = "";
		if(cmd_option_str("bigsize") != "") bigsize_str = "-D BIGSIZE=" + itos(cmd_option_int("bigsize")) + " ";


		// Compile code to BC
		cmd.str("");
		if(cmd_option_str("c_standard") == "C")
			cmd << "llvm-gcc " << cmd_option_str("compiler_flags") << " -O0 --emit-llvm -D NO_INIT " << bigsize_str << cflags << " -c file.c -o file.bc";
		else
			cmd << "llvm-g++ -O0 --emit-llvm -D NO_INIT " << bigsize_str << cflags << " -c file.cpp -o file.bc";
		systm(cmd.str().c_str());

	}

	if(cmd_option_bool("with_libs")){

		// Change name of standard functions
		cmd.str("");
		cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_function_names < file.bc > file-2.bc";
		systm(cmd.str().c_str());

		cmd.str("");
		cmd << "llvm-link " << tmp_file("file-2.bc") << " " << base_path << "/stdlibs/lib/library.bc -o " << tmp_file("file-3.bc") << ";";
		systm(cmd.str().c_str());

		cmd.str("");
		cmd << "mv " << tmp_file("file-3.bc") << " " << tmp_file("file.bc");
		systm(cmd.str().c_str());
	}

	if(cmd_option_bool("with_uclibs")){

		// rm list of functions 
		cmd.str("");
		cmd << "rm -f " << cmd_option_str("base_path") << "/stdlibs/list";
		systm(cmd.str());

		// rm list of globals
		//cmd.str("");
		//cmd << "rm -f " << cmd_option_str("base_path") << "/stdlibs/list2";
		//systm(cmd.str());

		// list functions and globals in stdlibs 

		vector<string> uclibs = cmd_option_string_vector("uclib");

		for( vector<string>::iterator it = uclibs.begin(); it != uclibs.end(); it++ ){
			//printf("uclib %s\n", it->c_str());
			cmd.str("");
			cmd << "find " << base_path << "/stdlibs_uclib/ -name " << *it << ".os > " << tmp_file("filelib");
			systm(cmd.str());

			ifstream input(tmp_file("filelib").c_str());
			string line; input >> line;


			cmd.str("");
			cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestStdlibs.so -stdlibs_list_functions < " << line << " > /dev/null";
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "llvm-link " << tmp_file("file.bc") << " " << line << " -o " << tmp_file("file-2.bc") << ";";
			systm(cmd.str().c_str());

			cmd.str("");
			cmd << "mv " << tmp_file("file-2.bc") << " " << tmp_file("file.bc");
			systm(cmd.str().c_str());

		}

		cmd.str("");
		cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_function_names < file.bc > file-2.bc";
		systm(cmd.str().c_str());

		cmd.str("");
		cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -instr_fill_names < file-2.bc > file-3.bc";
		systm(cmd.str().c_str());


		cmd.str("");
		cmd << "mv " << tmp_file("file-3.bc") << " " << tmp_file("file.bc");
		systm(cmd.str().c_str());

	}

}

void run(){

	start_pass("run");


	string base_path   = cmd_option_str("base_path");
	string llvm_path   = cmd_option_str("llvm_path");
	string output_file = cmd_option_str("output_file");

	dump_forced_free_vars();
	dump_forced_free_hints();

	stringstream cmd;

	// Execute resulting file
	cmd.str("");
	cmd << "./" << output_file;


	struct timespec ping_time;
	struct timespec pong_time;
	clock_gettime(CLOCK_MONOTONIC, &ping_time);

	if(cmd_option_bool("driven_by_frontend")){
		drive_frontend();
	} else {
		systm(cmd.str().c_str());
	}

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e9;
	spent_time *= 1000;

	stringstream action;
	action << "insert into measurements values(\"time_ms\"," << (int)spent_time << ");";
	db_command( action.str() );
	


	minimal_test_vectors_to_db();

	end_pass("run");

}

void dump_forced_free_vars(){
	vector<string> forced_free_vars = cmd_option_string_vector("forced_free_var");

	stringstream filepath;

	filepath << tmp_file("free_vars");

	FILE* file = fopen(filepath.str().c_str(), "w");
	for( vector<string>::iterator it = forced_free_vars.begin(); it != forced_free_vars.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
}

void dump_forced_free_hints(){
	vector<string> forced_free_hints = cmd_option_string_vector("forced_free_hint");

	stringstream filepath;

	filepath << tmp_file("free_hints");

	FILE* file = fopen(filepath.str().c_str(), "w");
	for( vector<string>::iterator it = forced_free_hints.begin(); it != forced_free_hints.end(); it++ ){
		fprintf(file, "%s\n", it->c_str());
	}
	fclose(file);
	
}

void compare_libs(){

	stringstream cflags;
	cflags << "-I " << cmd_option_str("base_path") << "/stdlibs/include/ -L" << cmd_option_str("base_path") << "/stdlibs/lib";
	stringstream cmd;

	cmd.str("");
	cmd << "llvm-g++ --emit-llvm " << prj_file(cmd_option_string_vector("file")[0]) << " -c -o " << tmp_file("file-1.bc") << ";";
	systm(cmd.str());

	cmd.str("");
	cmd << "llvm-g++ --emit-llvm " << cflags.str() << " " << prj_file(cmd_option_string_vector("file")[0]) << " -c -o " << tmp_file("file-2.bc") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "llvm-dis " << tmp_file("file-1.bc") << " -o " << tmp_file("file-1.ll") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "llvm-link " << tmp_file("file-2.bc") << " " << cmd_option_str("base_path") << "/stdlibs/lib/library.bc" << " -o " << tmp_file("file-3.bc") << ";";
	systm(cmd.str());

	cmd.str("");
	cmd << "llvm-dis " << tmp_file("file-3.bc") << " -o " << tmp_file("file-3.ll") << ";";
	systm(cmd.str());


	cmd.str("");
	cmd << "meld file-1.ll file-3.ll";
	systm(cmd.str());


	

}

void list_external_functions(){
	make_initial_bc();

	string llvm_path = cmd_option_str("llvm_path");

	stringstream cmd;
	cmd.str("");
	cmd << "opt -load " << llvm_path << "/Release+Asserts/lib/ForestInstr.so -list_external_functions < file.bc";
	systm(cmd.str().c_str());

}

void linked_bc(){
	make_initial_bc();

	stringstream command;
	command << "mv " << tmp_file("file.bc") << " " << prj_file("file.bc");
	systm(command.str());
}

void create_tmp_path(){
	stringstream action;
	action << "mkdir -p " << tmp_dir();
	system(action.str().c_str());
}

void show_timer(){
	systm("echo 'select * from timer;' | sqlite3 database.db > timer_file;");

	ifstream input(tmp_file("timer_file").c_str());
	string line;

	map<string, float> times;
	
	while( getline( input, line ) ) {
		vector<string> tokens = tokenize(line, "|");
		string id = tokens[0];
		float time = stof(tokens[1]);
		times[id] += time;
	}

	FILE* file = fopen(tmp_file("gnuplot_data").c_str(), "w");
	int n = 1;
	float max_val = -9999;
	int max_len = 0;
	for( map<string,float>::iterator it = times.begin(); it != times.end(); it++ ){
		fprintf(file,"%d %f %s\n",n++, it->second, it->first.c_str());
		if(it->second > max_val)
			max_val = it->second;
		if(it->first.length() > max_len)
			max_len = it->first.length();
	}
	fclose(file);

	float min_x = max_val/480.0*max_len*15;

	printf("max_val %f max_len %d min_x %f\n", max_val, max_len, min_x);

	file = fopen(tmp_file("gnuplot_script").c_str(), "w");
	fprintf(file, "set terminal png size '%lux8000'\n", times.size()*20);
	fprintf(file, "set output 'demo.png'\n");
	fprintf(file, "set nokey\n");
	fprintf(file, "unset border\n");
	fprintf(file, "unset xtics\n");
	fprintf(file, "set yrange [-%f:%f]\n",min_x, max_val);
	//fprintf(file, "set yrange [-%d:%f]\n",max_len*250, max_val);
	fprintf(file, "plot 'gnuplot_data' using 1:(-1):3 with labels rotate right, \\\n");
	fprintf(file, "     'gnuplot_data' using 1:2 with boxes	\n");
	fclose(file);

	systm("gnuplot gnuplot_script");
	systm("convert -rotate 90 demo.png demo2.png");
	systm("eog demo2.png");
	
	
}

void show_exceptions(){
	stringstream cmd;

	printf("\e[31m == Exceptions == \e[0m\n");
	cmd.str("");
	cmd << ".mode columns\\n.width 5 10\\n.headers on\\nselect * from exceptions;";
	db_command_visible(cmd.str());
	printf("\n");

	printf("\e[31m == Assignments == \e[0m\n");
	cmd.str("");
	cmd << ".mode columns\\n.width 5 30 5\\n.headers on\\nselect problem_id, name_hint, value from results where problem_id = (select problem_id from exceptions);";
	db_command_visible(cmd.str());
	printf("\n");

}

void show_interpolants(){
	stringstream cmd;

	cmd << ".mode columns\\n.width 20 100 \\n.headers on\\n";
	cmd << "select distinct * from interpolants order by position;";
	db_command_visible(cmd.str());
	printf("\n");

}

