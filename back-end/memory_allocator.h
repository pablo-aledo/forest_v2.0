/*
 * =====================================================================================
 * /
 * |     Filename:  memory_allocator.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  06/22/2015 02:33:17 PM
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

#ifndef _MEM_ALLOCA_H_
#define _MEM_ALLOCA_H_

using namespace std;

class MemAlloc {
public:
	void fr_free(char* register_pointer);
	MemAlloc ();
	virtual ~MemAlloc ();
	void* fr_malloc(char* register_size);
	void* fr_alloca(char* register_size);
	void initialize();
	void end_sim();

private:
	int get_size();
	int number_of_mallocs;
	
};


#endif /* end of include guard: _MEM_ALLOCA_H_*/

