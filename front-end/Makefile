all: ../bin/forest

../bin/forest: ../build/forest.o ../build/tinystr.o ../build/tinyxml.o ../build/tinyxmlerror.o ../build/tinyxmlparser.o ../build/cmd_options.o ../build/utils_frontend.o ../build/pass_handler.o ../build/bc_handling.o ../build/coverage.o ../build/database_frontend.o ../build/heuristic.o ../build/klee.o ../build/svcomp.o ../build/random_testing.o ../build/models.o ../build/uppaal_frontend.o ../build/goanna_fpr.o ../build/concurrent.o
	g++ ../build/forest.o ../build/tiny*.o ../build/cmd_options.o ../build/utils_frontend.o ../build/pass_handler.o ../build/bc_handling.o ../build/coverage.o ../build/database_frontend.o ../build/heuristic.o ../build/klee.o ../build/svcomp.o ../build/random_testing.o ../build/models.o ../build/uppaal_frontend.o ../build/goanna_fpr.o ../build/concurrent.o -o ../bin/forest -lrt -I/usr/include/libxml2/ -lxml2

../build/forest.o: forest.cpp 
	g++ -g -c forest.cpp -o ../build/forest.o

../build/tinystr.o: tinystr.cpp 
	g++ -g -c tinystr.cpp -o ../build/tinystr.o

../build/tinyxml.o: tinyxml.cpp 
	g++ -g -c tinyxml.cpp -o ../build/tinyxml.o

../build/tinyxmlerror.o: tinyxmlerror.cpp 
	g++ -g -c tinyxmlerror.cpp -o ../build/tinyxmlerror.o


../build/tinyxmlparser.o: tinyxmlparser.cpp 
	g++ -g -c tinyxmlparser.cpp -o ../build/tinyxmlparser.o 

../build/cmd_options.o: cmd_options.cpp
	g++ -g -c cmd_options.cpp -o ../build/cmd_options.o

../build/utils_frontend.o: utils_frontend.cpp
	g++ -g -c utils_frontend.cpp -o ../build/utils_frontend.o

../build/pass_handler.o: pass_handler.cpp
	g++ -g -c pass_handler.cpp -o ../build/pass_handler.o

../build/bc_handling.o: bc_handling.cpp
	g++ -g -c bc_handling.cpp -o ../build/bc_handling.o

../build/coverage.o: coverage.cpp
	g++ -g -c coverage.cpp -o ../build/coverage.o

../build/database_frontend.o: database_frontend.cpp
	g++ -g -c database_frontend.cpp -o ../build/database_frontend.o

../build/heuristic.o: heuristic.cpp
	g++ -g -c heuristic.cpp -o ../build/heuristic.o

../build/klee.o: klee.cpp
	g++ -g -c klee.cpp -o ../build/klee.o

../build/svcomp.o: svcomp.cpp
	g++ -g -c svcomp.cpp -o ../build/svcomp.o

../build/random_testing.o: random_testing.cpp
	g++ -g -c random_testing.cpp -o ../build/random_testing.o

../build/models.o: models.cpp
	g++ -g -c models.cpp -o ../build/models.o

../build/uppaal_frontend.o: uppaal.cpp
	g++ -g -c uppaal.cpp -o ../build/uppaal_frontend.o -I/usr/include/libxml2/ -lxml2

../build/goanna_fpr.o: goanna_fpr.cpp
	g++ -g -c goanna_fpr.cpp -o ../build/goanna_fpr.o

../build/concurrent.o: concurrent.cpp 
	g++ -g -c concurrent.cpp -o ../build/concurrent.o


