/*
 * =====================================================================================
 * /
 * |     Filename:  z3_w.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  07/10/2014 04:27:51 PM
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
#include <sstream>
#include <string>
#include <unistd.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <iostream>
#include <fstream>

using namespace std;


int main(int argc, const char *argv[])
{
	stringstream argvs;

	for ( unsigned int i = 2; i < argc; i++) {
		argvs << string(argv[i]) << " ";
	}

	if(pid_t pid = fork()){

		struct timespec ping_time;
		clock_gettime(CLOCK_MONOTONIC, &ping_time);

		while(true){

			struct timespec pong_time;
			clock_gettime(CLOCK_MONOTONIC, &pong_time);

			float spent_time = 0;
			spent_time += pong_time.tv_sec - ping_time.tv_sec;
			spent_time *= 1e9;
			spent_time += pong_time.tv_nsec - ping_time.tv_nsec;
			spent_time /= 1e9;

			int status;
			pid_t result = waitpid(pid, &status, WNOHANG);
			if( spent_time > (float)(atoi(argv[1]))){
				kill(pid, 9);
				system("killall z3");
				printf("unknown\n");
				return 0;
			}

			if(result){
				return 0;
			}

			usleep(1000);
		}
	} else {

		system( ( "z3 " + argvs.str() ).c_str() );
	}

	return 0;
}
