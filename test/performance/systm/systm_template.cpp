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
#include <stdlib.h>
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>

using namespace std;

#define N 50
#define ZEROS %n%

void mult(int A[N][N], int B[N][1], int C[N][1], int rows1, int cols1, int rows2, int cols2){
	for ( int r = 0 ; r < rows1 ; r++ ) {
		for ( int c = 0 ; c < cols2 ; c++ ) {
			int sum = 0;
			for ( int k = 0 ; k < cols1; k++ ) {
				sum = sum + A[r][k]*B[k][c];
			}

			C[r][c] = sum;
		}
	}
}

bool cmp(int C[N][1], int X[N][1], int rows, int cols){
	for ( unsigned int i = 0; i < rows; i++) {
		for ( unsigned int j = 0; j < cols; j++) {
			if( C[i][j] != X[i][j] ) return false;
		}
	}

	return true;
}

int e;

void rand_matrix(int A[N][N], int rows, int cols){
	for ( unsigned int i = 0; i < rows; i++) {
		for ( unsigned int j = 0; j < cols; j++) {
			A[i][j] = rand()%1000;
		}
	}
}

void rand_col(int A[N][1], int rows){
	for ( unsigned int i = 0; i < rows; i++) {
		A[i][0] = rand()%1000;
	}
}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

string itos_x(int i){

	char b[20];
	sprintf(b, "#x%08x", i);
	return string(b);
}

void out_problm_real(int A[N][N], int C[N][1], int rows, int cols){

	FILE* file = fopen("/tmp/problem_real.smt2", "w");

	fprintf(file, "(set-option :produce-models true)\n");
	fprintf(file, "(set-logic AUFNIRA)\n");

	for ( unsigned int c = 0; c < cols; c++) {
		fprintf(file, "(declare-fun x%d () Real)\n", c);
	}


	for ( int f = 0 ; f < rows; f++ ) {
		string out;
		//if(f == rows-1)
			//out = "(assert (>= (+ ";
		//else
			out = "(assert (= (+ ";

		for ( int c = 0 ; c < cols; c++ ) {

			out += "(* " + itos(A[f][c]) + " x" + itos(c) + ") ";

		}
		out += ") " + itos(C[f][0]) + ")";

		fprintf(file, "%s)\n", out.c_str());
	}

	fprintf(file, "(check-sat)\n");

	fclose(file);


}


void out_problm_int(int A[N][N], int C[N][1], int rows, int cols){

	FILE* file = fopen("/tmp/problem_int.smt2", "w");

	fprintf(file, "(set-option :produce-models true)\n");
	fprintf(file, "(set-logic AUFNIRA)\n");

	for ( unsigned int c = 0; c < cols; c++) {
		fprintf(file, "(declare-fun x%d () Int)\n", c);
	}


	for ( int f = 0 ; f < rows; f++ ) {
		string out;
		//if(f == rows-1)
			//out = "(assert (>= (+ ";
		//else
			out = "(assert (= (+ ";

		for ( int c = 0 ; c < cols; c++ ) {

			out += "(* " + itos(A[f][c]) + " x" + itos(c) + ") ";

		}
		out += ") " + itos(C[f][0]) + ")";

		fprintf(file, "%s)\n", out.c_str());
	}

	fprintf(file, "(check-sat)\n");

	fclose(file);


}


void out_problm_ineq_real(int A[N][N], int C[N][1], int rows, int cols){

	FILE* file = fopen("/tmp/problem_ineq_real.smt2", "w");

	fprintf(file, "(set-option :produce-models true)\n");
	fprintf(file, "(set-logic AUFNIRA)\n");

	for ( unsigned int c = 0; c < cols; c++) {
		fprintf(file, "(declare-fun x%d () Real)\n", c);
	}


	for ( int f = 0 ; f < rows; f++ ) {
		string out;
		out = "(assert (<= (+ ";

		for ( int c = 0 ; c < cols; c++ ) {

			out += "(* " + itos(A[f][c]) + " x" + itos(c) + ") ";

		}
		out += ") " + itos(C[f][0]) + ")";

		fprintf(file, "%s)\n", out.c_str());
	}

	fprintf(file, "(check-sat)\n");

	fclose(file);


}


void out_problm_bv(int A[N][N], int C[N][1], int rows, int cols){

	FILE* file = fopen("/tmp/problem_bv.smt2", "w");

	fprintf(file, "(set-option :produce-models true)\n");

	for ( unsigned int c = 0; c < cols; c++) {
		fprintf(file, "(declare-const x%d (_ BitVec 32))\n", c);
	}


	for ( int f = 0 ; f < rows; f++ ) {
		string out = "(assert (= (bvadd ";
		for ( int c = 0 ; c < cols; c++ ) {

			out += "(bvmul " + itos_x(A[f][c]) + " x" + itos(c) + ") ";

		}
		out += ") " + itos_x(C[f][0]) + ")";

		fprintf(file, "%s)\n", out.c_str());
	}

	fprintf(file, "(check-sat)\n");

	fclose(file);


}

void get_time_real(){


	struct timespec ping_time;
	struct timespec pong_time;
	
	clock_gettime(CLOCK_MONOTONIC, &ping_time);
	system("z3 /tmp/problem_real.smt2 >/dev/null");
	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e6;

	printf("%f ", spent_time);
	
}

void get_time_int(){


	struct timespec ping_time;
	struct timespec pong_time;
	
	clock_gettime(CLOCK_MONOTONIC, &ping_time);
	system("z3 /tmp/problem_int.smt2 >/dev/null");
	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e6;

	printf("%f ", spent_time);
	
}


void get_time_ineq_real(){


	struct timespec ping_time;
	struct timespec pong_time;
	
	clock_gettime(CLOCK_MONOTONIC, &ping_time);
	system("z3 /tmp/problem_ineq_real.smt2 >/dev/null");
	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e6;

	printf("%f ", spent_time);
	
}

void get_time_bv(){


	struct timespec ping_time;
	struct timespec pong_time;
	
	clock_gettime(CLOCK_MONOTONIC, &ping_time);
	system("z3 /tmp/problem_bv.smt2 >/dev/null");
	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	
	float spent_time = 0;
	spent_time += pong_time.tv_sec - ping_time.tv_sec;
	spent_time *= 1e9;
	spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
	spent_time /= 1e6;

	printf("%f ", spent_time);
	
}

void zeros(int A[N][N], int rows, int cols){


	vector<pair<int, int> > vect;

	for ( unsigned int i = 0; i < rows; i++) {
		for ( unsigned int j = 0; j < cols; j++) {
			pair<int, int> a = pair<int, int>(i,j);
			vect.push_back(a);
		}
	}

	random_shuffle ( vect.begin(), vect.end() );


	for ( unsigned int i = 0; i < ZEROS; i++) {
		A[vect[i].first][vect[i].second] = 0;
	}
}









/* This function exchange two rows of a matrix */

void swap(int mat[N][N], int row1,int row2, int col)
{
    for( int i = 0; i < col; i++)
    {
        int temp = mat[row1][i];
        mat[row1][i] = mat[row2][i];
        mat[row2][i] = temp;
    }
}

/* This function find rank of matrix */

int Rank_Mat(int mat[N][N],int row1, int col1) {
    int r, c;
    for(r = 0; r< col1; r++) {
        if( mat[r][r] ){  // Diagonal element is not zero
		for(c = 0; c < row1; c++){
			if(c != r) {
				/* Make all the elements above and below the current principal
				   diagonal element zero */

				float ratio = mat[c][r]/ mat[r][r];
				for( int i = 0; i < col1; i++)
					mat[c][i] -= ratio * mat[r][i];
			}

		}
	} else {
            for(c =  r+1 ; c < row1;  c++)
                if (mat[c][r])
                {
                    /*  Find non zero elements in the same column */
                    swap(mat, r,c,col1);
                    break ;
                }

            if(c == row1)
            {
                -- col1;

                for(c = 0; c < row1; c ++)
                    mat[c][r] = mat[c][col1];
            }
            --r;
        }
    }
    return col1;
}




void get_rank(int A[N][N], int rows, int cols){
	printf("%d ", Rank_Mat(A, rows, cols));
}

int main() {
	srand(4242);
	int A[N][N];
	int B[N][1];
	int C[N][1];
	int X[N][1] = {17,39};


	rand_matrix(A, N, N);
	zeros(A,N,N);
	rand_col(B, N);
	mult(A, B, C, N,N,N,1);

	//printf("A=\n");
	//for ( unsigned int r = 0; r < 4; r++) {
		//for ( unsigned int c = 0; c < 4; c++) {
			//printf("%d ", A[r][c]);
		//} printf("\n");
	//}
	//printf("B=\n");
	//for ( unsigned int r = 0; r < 4; r++) {
		//printf("%d\n", B[r][0]);
	//}
	//printf("C=\n");
	//for ( unsigned int r = 0; r < 4; r++) {
		//printf("%d\n", C[r][0]);
	//}


	out_problm_real(A, C, N, N);
	//out_problm_int(A, C, N, N);
	//out_problm_ineq_real(A, C, N, N);
	//out_problm_bv(A, C, N, N);

	get_time_real();
	get_rank(A,N,N);
	//get_time_int();
	//get_time_ineq_real();
	//get_time_bv();
	printf("\n");


	/*printf("%d\n%d\n", C[0][0], C[1][0]);*/
	if(cmp(C, X, 2, 1))
		return 1;
	else
		return 0;
}
