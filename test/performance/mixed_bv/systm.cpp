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
#define LIN_VAR 25
#define NSAMPLES 3
#define N_BITS 8
#define ASSERTIONS N
#define MAX_TRIES 1
#define BV_CORRELATION 1
#define ZEROS 1


#define BITS_4 "4"

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
		case 1: return "bvslt";
		case 2: return "bvsgt";
	}
}

string bv(int x){

	string ret;
	for(int i=N_BITS-1; i>=0; i--) {
		(x & (1 << i)) ? ret+='1' : ret+='0';
	}

	return "#b" + ret;

	//printf("\n");
	//char ret[100];
	//sprintf(ret, "#x%0" BITS_4 "x", i );
	//return string(ret);
}



string bv_rand(){
	stringstream ret;
	ret << "#b";
	for ( unsigned int i = 0; i < N_BITS; i++) {
		ret << rand()%2;
	}

	return ret.str();
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

		fprintf(file, "; Declaration of variables\n");
		for ( unsigned int c = 0; c < LIN_VAR; c++) {
			fprintf(file, "(declare-const x%d (_ BitVec %d))\n", c, N_BITS);
		}

		fprintf(file, "; Linear Constraints\n");
		for ( int f = 0 ; f < ASSERTIONS; f++ ) {
			stringstream out;

			out << "(assert (" << rand_polarity() << " (bvadd ";

			for ( int c = 0 ; c < LIN_VAR; c++ ) {

				out << "(bvmul " << bv(A[f][c]) << " x" << c << ") ";

			}
			out << ") " << bv(C[f]) << ")";

			fprintf(file, "%s)\n", out.str().c_str());
		}


		fprintf(file, "; Boolean Constraints\n");
		for ( int f = 0 ; f < BV_VAR; f++ ) {
			stringstream out;

			out << "(assert (= " << "x" << f << " (bvand ";
			out << "(bvadd ";
			for ( unsigned int i = BV_VAR; i < BV_VAR + BV_CORRELATION; i++) {
				out << "(bvmul " << bv_rand() << " x" << rand()%(LIN_VAR-BV_VAR)+BV_VAR << ") ";
			}
			out << ") ";

			out << "(bvadd ";
			for ( unsigned int i = BV_VAR; i < LIN_VAR; i++) {
				out << "(bvmul " << bv_rand() << " x" << i << ") ";
			}
			out << ") ";

			out << ")))";

			fprintf(file, "%s\n", out.str().c_str());
		}


		fprintf(file, "(check-sat)\n");

		fclose(file);
		system(("z3_timed 300 /tmp/problem_" + itos(j) + ".smt2 > /tmp/output").c_str());
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
		system(("z3_timed 300 /tmp/problem_" + itos(i) + ".smt2 >/dev/null").c_str());
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
	srand(4243);

	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		out_problm();
	}
	get_time();
	printf(" %d %d", sat, unsat);
	printf("\n");

	return 0;
}
