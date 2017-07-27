/*
 * =====================================================================================
 * /
 * |     Filename:  systm.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  05/21/2014 12:29:48 PM
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

#include <stdio.h>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>

using namespace std;

#define BV_VAR 3
#define LIN_VAR 10
#define NSAMPLES 30
#define N_BITS 10
#define ASSERTIONS N
#define MAX_TRIES 1
#define BV_CORRELATION 1
#define ZEROS 1



void gen_matrix();
int A[ASSERTIONS][LIN_VAR];
int B[LIN_VAR];
int C[ASSERTIONS];


string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

string rand_polarity(){
	return "=";
	switch (rand()%3) {
		case 0: return "=";
		case 1: return ">";
		case 2: return "<";
		default: return "=";
	}
}

int sat = 0;
int unsat = 0;

void out_problm(){

	static int j;
	bool is_sat = 0;
	int ntries = 0;

	while(true){

		gen_matrix();

		FILE* file = fopen(("/tmp/problem_" + itos(j) + ".smt2").c_str(), "w");

		fprintf(file, "(set-option :produce-models true)\n");
		fprintf(file, "(set-logic AUFNIRA)\n");

		fprintf(file, "; Declaration of variables\n");
		for ( unsigned int c = 0; c < BV_VAR; c++) {
			for ( unsigned int d = 0; d < N_BITS; d++) {
				fprintf(file, "(declare-fun a_%d_%d () Int)\n", c, d);
				fprintf(file, "(declare-fun b_%d_%d () Int)\n", c, d);
				fprintf(file, "(declare-fun c_%d_%d () Int)\n", c, d);
			}
		}



		fprintf(file, "; Declaration of linear variables\n");
		for ( unsigned int c = 0; c < LIN_VAR; c++) {
			fprintf(file, "(declare-fun x%d () Int)\n", c);
		}




		fprintf(file, "; Boolean limits\n");
		for ( unsigned int c = 0; c < BV_VAR; c++) {
			for ( unsigned int d = 0; d < N_BITS; d++) {
				fprintf(file, "(assert (and (<= 0 a_%d_%d) (<= a_%d_%d 1)))\n", c, d, c, d);
				fprintf(file, "(assert (and (<= 0 b_%d_%d) (<= b_%d_%d 1)))\n", c, d, c, d);
			}
		}

		fprintf(file, "; Boolean operation\n");
		for ( unsigned int c = 0; c < BV_VAR; c++) {
			for ( unsigned int d = 0; d < N_BITS; d++) {
				fprintf(file, "(assert (= c_%d_%d (* a_%d_%d b_%d_%d)))\n", c, d, c, d, c, d);
			}
		}

		fprintf(file, "; Mapping\n");
		for ( int f = 0 ; f < BV_VAR; f++ ) {
			stringstream out1;
			stringstream out2;

			out1 << "(assert (= (+ ";
			out2 << "(assert (= (+ ";

			for ( int c = 0 ; c < N_BITS; c++ ) {

				out1 << "(* " << itos(1 << c) << " a_" << f << "_" << c << ") ";
				out2 << "(* " << itos(1 << c) << " b_" << f << "_" << c << ") ";

			}
			for ( int c = BV_VAR ; c < BV_VAR + BV_CORRELATION; c++ ) {

				out1 << "(* -" << rand()%100 << " x" << rand()%(LIN_VAR-BV_VAR)+BV_VAR << ") ";
				out2 << "(* -" << rand()%100 << " x" << rand()%(LIN_VAR-BV_VAR)+BV_VAR << ") ";

			}
			
			out1 << ") 0" << "))";
			out2 << ") 0" << "))";

			fprintf(file, "%s\n", out1.str().c_str());
			fprintf(file, "%s\n", out2.str().c_str());
		}

		fprintf(file, "; Linear Constraints\n");
		for ( int f = 0 ; f < ASSERTIONS; f++ ) {
			stringstream out;

			out << "(assert (" << rand_polarity() << " (+ ";

			for ( int c = 0 ; c < LIN_VAR; c++ ) {
				if(c < BV_VAR){
					int var = rand()%BV_VAR;
					for ( unsigned int i = 0; i < N_BITS; i++) {
						//out << "(* " << rand()%100 << " c_" << var << "_" << i << ") ";
						out << "(* " << rand()%100 << " c_" << c   << "_" << i << ") ";
					}
				} else {
					//out << "(* " << rand_val() << " x" << c << ") ";
					out << "(* " << A[f][c] << " x" << c << ") ";
				}


			}
			//out << ") " << rand_val() << ")";
			out << ") " << C[f] << ")";

			fprintf(file, "%s)\n", out.str().c_str());
		}


		fprintf(file, "(check-sat)\n");

		fclose(file);
		system(("z3 /tmp/problem_" + itos(j) + ".smt2 > /tmp/output").c_str());
		ifstream input("/tmp/output");
		string line;
		getline( input, line );
		is_sat = (line == "sat");
		//if(j <  NSAMPLES/2 && !is_sat) break;
		//if(j >= NSAMPLES/2 &&  is_sat) break;
		//if( ntries++ == MAX_TRIES) break;
		break;

	}

	if(is_sat) sat++;
	if(!is_sat) unsat++;

	j++;

}



void get_time(){


	struct timespec ping_time;
	struct timespec pong_time;
	float time_all = 0;
	
	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		clock_gettime(CLOCK_MONOTONIC, &ping_time);
		system(("z3 /tmp/problem_" + itos(i) + ".smt2 >/dev/null").c_str());
		clock_gettime(CLOCK_MONOTONIC, &pong_time);

		float spent_time = 0;
		spent_time += pong_time.tv_sec - ping_time.tv_sec;
		spent_time *= 1e9;
		spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
		spent_time /= 1e6;
		time_all += spent_time;
	}

	printf("%f", time_all/(float)NSAMPLES);
	
}

void gen_matrix(){
	// A
	for ( unsigned int i = 0; i < ASSERTIONS; i++) {
		for ( unsigned int j = 0; j < LIN_VAR; j++) {
			A[i][j] = rand()%1000;
		}
	}

	// zeros
	vector<pair<int, int> > vect;
	for ( unsigned int i = 0; i < ASSERTIONS; i++) {
		for ( unsigned int j = 0; j < LIN_VAR; j++) {
			pair<int, int> a = pair<int, int>(i,j);
			vect.push_back(a);
		}
	}
	random_shuffle ( vect.begin(), vect.end() );
	for ( unsigned int i = 0; i < ZEROS; i++) {
		A[vect[i].first][vect[i].second] = 0;
	}


	// B
	for ( unsigned int i = 0; i < ASSERTIONS; i++) {
		B[i] = rand()%1000;
	}

	// C
	for ( int r = 0 ; r < ASSERTIONS; r++ ) {
		int sum = 0;
		for ( int k = 0 ; k < LIN_VAR; k++ ) {
			sum = sum + A[r][k]*B[k];
		}

		C[r] = sum;
		//C[r] = rand()%1000;
	}

}

int main() {
	srand(4247);

	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		out_problm();
	}
	get_time();
	printf(" %d %d\n", sat, unsat);
	printf("\n");

	return 0;
}
