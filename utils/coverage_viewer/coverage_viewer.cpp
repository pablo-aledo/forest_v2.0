#include <gtk/gtk.h>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <map>
#include <iostream>
#include <fstream>
#include <vector>

using namespace std;

GtkWidget *image;
GtkWidget *window;

#define SIZE_STR 1000

void generate_dot_file(){

	stringstream command;

	command << "cd " << tmp_dir();
	command << "opt -dot-cfg < file.bc >/dev/null 2>/dev/null;";
	command << "mv cfg.main.dot coverage.dot";
	system(command.str().c_str());
	
}

vector<string> tokenize(const string& str,const string& delimiters) {
	vector<string> tokens;
    	
	// skip delimiters at beginning.
    	string::size_type lastPos = str.find_first_not_of(delimiters, 0);
    	
	// find first "non-delimiter".
    	string::size_type pos = str.find_first_of(delimiters, lastPos);

    	while (string::npos != pos || string::npos != lastPos)
    	{
		// found a token, add it to the vector.
		tokens.push_back(str.substr(lastPos, pos - lastPos));
	
		// skip delimiters.  Note the "not_of"
		lastPos = str.find_first_not_of(delimiters, pos);
	
		// find next "non-delimiter"
		pos = str.find_first_of(delimiters, lastPos);
    	}

	return tokens;
}

int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}

map<string, int> load_coverages(){

	map<string, int> ret;

	stringstream command;
	command << "echo 'select * from visualization_bbs;' | sqlite3 " << tmp_file("database.db") << " > " << tmp_file("visualization_bbs") << " 2>/dev/null";
	system(command.str().c_str());

	ifstream input(tmp_file("visualization_bbs").c_str());
	string line;
	
	while( getline( input, line ) ) {
		string name  = tokenize(line, "|")[0];
		string count = tokenize(line, "|")[1];
		ret[name] = stoi(count);
	}
	
	return ret;
}

string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

void update_dot_file(){

	map<string, int> coverages;
	stringstream command;

	while(!coverages.size()){
		coverages = load_coverages();
	}

	command << "cd " << tmp_dir() << "; cat coverage.dot | sed ";

	int max = 1;
	for( map<string,int>::iterator it = coverages.begin(); it != coverages.end(); it++ ){
		max = it->second>max?it->second:max;
	}

	for( map<string,int>::iterator it = coverages.begin(); it != coverages.end(); it++ ){
		string color = "\\/rdylgn9\\/" + itos(it->second*8/max+1);
		string to_add = "style=\"filled\",fillcolor=\"" + color + "\"";
		command << "-e 's/label=\"{" << it->first << ":/" << to_add << ",label=\"{" << it->first << ":/g' ";
	}
	command << " > coverage_2.dot";

	system(command.str().c_str());

}

void generate_png(){
	stringstream command;

	command << "cd " << tmp_dir() << ";";
	command << "dot -Tpng coverage_2.dot > coverage.png 2>/dev/null;";
	command << "convert -resize 700x700 coverage.png coverage_2.png;";
	command << "mv coverage_2.png coverage.png;";

	system(command.str().c_str());

}


static gboolean time_handler(GtkWidget *widget) {

	update_dot_file();
	generate_png();

	gtk_widget_destroy(image);
	image = gtk_image_new_from_file(tmp_file("coverage.png"));
	gtk_container_add(GTK_CONTAINER(window), image);
	gtk_widget_show_all(window);

	return TRUE;
}

void wait_for_bc(){


	while( access( tmp_file("file.bc").c_str(), F_OK ) == -1 ) {
		;
	}

}

int main( int argc, char *argv[]) {


	wait_for_bc();

	generate_dot_file();
	update_dot_file();
	generate_png();

	gtk_init(&argc, &argv);

	window = gtk_window_new(GTK_WINDOW_TOPLEVEL);

	gtk_window_set_position(GTK_WINDOW(window), GTK_WIN_POS_CENTER);
	gtk_window_set_default_size(GTK_WINDOW(window), 230, 150);
	gtk_window_set_title(GTK_WINDOW(window), "Image");
	gtk_window_set_resizable(GTK_WINDOW(window), FALSE);
	gtk_container_set_border_width(GTK_CONTAINER(window), 2);

	image = gtk_image_new_from_file(tmp_file("coverage.png").c_str());
	gtk_container_add(GTK_CONTAINER(window), image);
	gtk_widget_show_all(window);


	g_signal_connect(G_OBJECT(window), "destroy", G_CALLBACK(gtk_main_quit), NULL);
	g_timeout_add(3000, (GSourceFunc) time_handler, NULL);
	gtk_main();

	return 0;
}
