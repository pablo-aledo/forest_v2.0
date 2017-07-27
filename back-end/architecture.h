/*
 * =====================================================================================
 * /
 * |     Filename:  architecture.h
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/28/2014 01:07:13 PM
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

string hex_representation(int in, string type);
string hex_representation_2(int in, string type);
unsigned int bits(string type);
int get_n_bits(string type);
string internal_representation_int(int in, string type, string solver);
string internal_representation_float(float in, string type, string solver);
int primary_size( string type_str );
int get_size(string type);
string concat_begin(int size_bits, int num);
string sign_ext(int bits_src, int bits_dst, string content);
string zero_ext(int bits_src, int bits_dst, string content);
string trunc(string src, string dst_type);
string make_unsigned(string value, string type);
string make_signed(string value, string type);
