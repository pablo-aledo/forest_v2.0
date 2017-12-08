#include <systemc.h>

SC_MODULE(mand_gm){
	sc_in<bool> a;
	sc_in<bool> b;
	sc_out<bool> c;

	SC_CTOR(mand_gm){
		SC_METHOD(fun);
		sensitive << a << b;
	}

	void fun(){
		c.write(a & b);
	}
};

SC_MODULE(mand_debug){
	sc_in<bool> a;
	sc_in<bool> b;
	sc_out<bool> c;

	SC_CTOR(mand_debug){
		SC_METHOD(fun);
		sensitive << a << b;
	}

	void fun(){
		c.write(~(a & b));
	}
};

int sc_main (int argc, char ** argv) {

	mand_gm  gm("mand_gm");
    mand_debug  debug("mand_debug");
	sc_signal<bool> a;
	sc_signal<bool> b;
	sc_signal<bool> c_gm;
    sc_signal<bool> c_debug;

	gm.a(a);
	gm.b(b);
	gm.c(c_gm);
    
    debug.a(a);
	debug.b(b);
	debug.c(c_debug);

	a = 0;
	b = 1;

	sc_start(1, SC_MS);
    
    if (c_gm == c_debug){
        return 0;
    } else {
        return -1;
    }
}
