/*
 * =====================================================================================
 * /
 * |     Filename:  timer.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/28/2014 09:06:04 AM
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

#include "timer.h"

Timer::Timer(){

	n=0;
	spent_time_ms = 0;
	
}

Timer::~Timer(){
	
}

void Timer::start_timer(){

	
	clock_gettime(CLOCK_MONOTONIC, &(ping_time[n]));

	n++;
	

}

void Timer::end_timer(string id){

	n--;

	clock_gettime(CLOCK_MONOTONIC, &pong_time);
	
	spent_time_ms = 0;
	spent_time_ms += pong_time.tv_sec - (ping_time[n]).tv_sec;
	spent_time_ms *= 1e9;
	spent_time_ms += pong_time.tv_nsec - (ping_time[n]).tv_nsec;
	spent_time_ms /= 1e6;

	times[id] += spent_time_ms;

}

void Timer::print_times(){


	for( map<string,float>::iterator it = times.begin(); it != times.end(); it++ ){
		printf("Timer %s %f\n", it->first.c_str(), it->second);
	}
	
}

map<string, float> Timer::get_times(){
	return times;
}

