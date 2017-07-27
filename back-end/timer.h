/*
 * =====================================================================================
 * /
 * |     Filename:  timer.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/28/2014 09:07:20 AM
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


#ifndef _TIMER_H_
#define _TIMER_H_

#include <string>
#include <map>
#include <stdio.h>

using namespace std;

class Timer {
public:
	map<string, float> get_times();
	void print_times();
	Timer ();
	virtual ~Timer ();

	void start_timer();
	void end_timer(string id);

private:
	struct timespec ping_time[100];
	struct timespec pong_time;
	float spent_time_ms;
	map<string, float> times;
	int n;
};




#endif /* end of include guard: _CONCURRENCY_H_ */

