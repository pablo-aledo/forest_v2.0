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

#define ASSERTIONS N
#define N_VAR 10
#define NSAMPLES 30
#define BITS "128"
#define BITS_4 "32"
#define MAX_TRIES 10
#define ZEROS 5


void gen_matrix();
int A[ASSERTIONS][N_VAR];
int B[N_VAR];
int C[ASSERTIONS];



string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

string rand_polarity(){
	switch (rand()%3) {
		case 0: return "=";
		case 1: return "bvslt";
		case 2: return "bvsgt";
	}
}


string bv(int i){

	char ret[100];
	sprintf(ret, "#x%0" BITS_4 "x", i );
	return string(ret);
}


int sat = 0;
int unsat = 0;

void out_problm(){

	static int j;
	int ntries = 0;
	bool is_sat;

	while(true){

		gen_matrix();

		FILE* file = fopen(("/tmp/problem_" + itos(j) + ".smt2").c_str(), "w");

		fprintf(file, "(set-option :produce-models true)\n");

		for ( unsigned int c = 0; c < N_VAR; c++) {
			fprintf(file, "(declare-const x%d (_ BitVec %s))\n", c, BITS);
		}


		for ( int f = 0 ; f < ASSERTIONS; f++ ) {
			stringstream out;

			out << "(assert (" << rand_polarity() << " (bvadd ";

			for ( int c = 2 ; c < N_VAR; c++ ) {

				//out << "(bvmul " << bv_rand() << " x" << c << ") ";
				out << "(bvmul " << bv(A[f][c]) << " x" << c << ") ";

			}
			//out << ") " << bv_rand() << ")";
			out << ") " << bv(C[f]) << ")";

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
		//if(ntries++ > MAX_TRIES) break;
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
		for ( unsigned int j = 0; j < N_VAR; j++) {
			A[i][j] = rand()%500;
		}
	}

	// zeros
	vector<pair<int, int> > vect;
	for ( unsigned int i = 0; i < ASSERTIONS; i++) {
		for ( unsigned int j = 0; j < N_VAR; j++) {
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
		B[i] = rand()%500;
	}

	// C
	for ( int r = 0 ; r < ASSERTIONS; r++ ) {
		int sum = 0;
		for ( int k = 0 ; k < N_VAR; k++ ) {
			sum = sum + A[r][k]*B[k];
		}

		C[r] = sum;
		//C[r] = rand()%1000;
	}

}

int main() {
	srand(4242);

	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		out_problm();
	}
	get_time();
	printf(" %d %d", sat, unsat);
	printf("\n");

	return 0;
}
