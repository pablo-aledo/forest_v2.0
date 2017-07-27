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
#include <math.h>
#include <algorithm>

using namespace std;

#define ASSERTIONS N
#define N_VAR 10
#define NSAMPLES 30
#define MAX_TRIES 1
#define TIMEOUT "300"
#define ZEROS 0




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

string rand_val(){
	stringstream ret;
	//ret << rand()%100 << ".0";
	ret << rand()%100;
	return ret.str();
}

void out_problm(){

	static int j;
	bool is_sat = 0;
	int ntries = 0;
	
	while(true){

		gen_matrix();

		FILE* file = fopen(("/tmp/problem_" + itos(j) + ".smt2").c_str(), "w");

		//fprintf(file, "(set-option :produce-models true)\n");
		//fprintf(file, "(set-logic AUFLIRA)\n");

		for ( unsigned int c = 0; c < N_VAR; c++) {
			fprintf(file, "(declare-fun x%d () Int)\n", c);
		}


		for ( int f = 0 ; f < ASSERTIONS; f++ ) {
			stringstream out;

			out << "(assert (" << rand_polarity() << " (+ ";

			for ( int c = 0 ; c < N_VAR; c++ ) {

				//out << "(* " << rand_val() << " x" << c << ") ";
				out << "(* " << A[f][c] << " x" << c << ") ";

			}
			//out << ") " << rand_val() << ")";
			out << ") " << C[f] << ")";

			fprintf(file, "%s)\n", out.str().c_str());
		}

		fprintf(file, "(check-sat)\n");

		fclose(file);

		//{
		//	system(("./checkstall.sh /tmp/problem_" + itos(j) + ".smt2 > stall_out").c_str());
		//	ifstream input("stall_out");
		//	string line;
		//	getline( input, line );
		//	if(line == "stall") continue;
		//}
		

		//system(("z3_timed " TIMEOUT " /tmp/problem_" + itos(j) + ".smt2 > /tmp/output").c_str());
		system(("z3 /tmp/problem_" + itos(j) + ".smt2 > /tmp/output").c_str());
		ifstream input("/tmp/output");
		string line;
		getline( input, line );
		is_sat = (line == "sat");
		//bool is_unknown = (line == "unknown");
		//if(j <  NSAMPLES/2 && !is_sat) break;
		//if(j >= NSAMPLES/2 &&  is_sat) break;
		//if(is_unknown) continue;
		//if(ntries++ == MAX_TRIES) break;
		break;
	}

	if(is_sat) sat++;
	if(!is_sat) unsat++;

	j++;

}



void get_time(){


	struct timespec ping_time;
	struct timespec pong_time;
	vector<float> measures;
	
	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		clock_gettime(CLOCK_MONOTONIC, &ping_time);
		//system(("z3_timed " TIMEOUT " /tmp/problem_" + itos(i) + ".smt2 >/dev/null").c_str());
		system(("z3 /tmp/problem_" + itos(i) + ".smt2 >/dev/null").c_str());
		clock_gettime(CLOCK_MONOTONIC, &pong_time);

		float spent_time = 0;
		spent_time += pong_time.tv_sec - ping_time.tv_sec;
		spent_time *= 1e9;
		spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
		spent_time /= 1e6;
		measures.push_back(spent_time);
	}

	float mean = 0;
	for ( unsigned int i = 0; i < measures.size(); i++) {
		mean += measures[i];
	}
	mean /= (float)(measures.size());


	float stdv = 0;
	for ( unsigned int i = 0; i < measures.size(); i++) {
		stdv += (measures[i]-mean)*(measures[i]-mean);
	}
	stdv = sqrt(stdv);


	mean = 0; int m = 0;
	for ( unsigned int i = 0; i < measures.size(); i++) {
		//if( fabs(measures[i] - mean) < 5.0*stdv){
			mean += measures[i];
			m++;
		//}
	}
	mean /= (float)(m);


	printf("%f", mean);
	
}

void gen_matrix(){
	// A
	for ( unsigned int i = 0; i < ASSERTIONS; i++) {
		for ( unsigned int j = 0; j < N_VAR; j++) {
			A[i][j] = rand()%1000;
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
		B[i] = rand()%1000;
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
	srand(4243);


	for ( unsigned int i = 0; i < NSAMPLES; i++) {
		out_problm();
	}
	get_time();
	printf(" %d %d", sat, unsat);
	printf("\n");

	return 0;
}
