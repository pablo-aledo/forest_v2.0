.PHONY: test coverage_viewer

all: start frontend backend opt z3_wrapper repl coverage_viewer

start:
	mkdir -p bin build lib

z3_wrapper:
	make -C utils/z3_wrapper/ 

coverage_viewer:
	#make -C utils/coverage_viewer/

backend:
	make -C back-end

frontend:
	make -C front-end

repl:
	make -C repl

opt:
	make -C optim-pass
clean:
	rm -rf build/*
	make -C optim-pass clean

test:
	make -C test

distclean: clean
	rm -rf bin/* lib/*

src_clean: distclean clean
	find -name *.o -o -name uppaal.xml -o -name salida -delete
	rm -rf package/*
pack:
	make -C package

install:
	install -m 755 bin/forest /bin/
	install -m 755 bin/z3_timed /bin/
	install -m 755 bin/repl /bin/
	install -m 644 lib/forest.a /usr/lib/
	
