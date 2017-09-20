Forest implements symbolic execution of LLVM intermediate language and is able
to detect errors in programs developed in C. Forest transforms a program into a
set of SMT formulas describing each feasible path and decides these formulas
with a SMT solver. This enables to prove the satisfiability of reachability
conditions, buffer overflows, null pointer dereferences... Forest implements
different encodings of SMT formulas, according to different theories: linear
arithmetic, polynomials and generic bit-accurate and not bit-accurate
translations.

## Typical installation:

```
# needed dependencies
sudo apt-get install sqlite3 graphviz meld subversion cmake g++ python2.7

# z3
git clone https://git01.codeplex.com/z3
cd z3-*
./configure
python scripts/mk_make.py
cd build
make
sudo make install

# llvm-3.7
svn co http://llvm.org/svn/llvm-project/llvm/tags/RELEASE_371/final /usr/src/llvm-3.7
svn co http://llvm.org/svn/llvm-project/cfe/tags/RELEASE_371/final /usr/src/llvm-3.7/tools/clang
svn co http://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_371/final /usr/src/llvm-3.7/projects/libcxx
svn co http://llvm.org/svn/llvm-project/libcxxabi/tags/RELEASE_371/final /usr/src/llvm-3.7/projects/libcxxabi

cd /usr/src/llvm-3.7
mkd build
../configure --prefix=/usr/share/llvm-3.7
make -j `nproc`
sudo make install

# compile
make 

# add bin to path
export PATH=$(pwd)/bin/:$PATH

# set environment variables
export LLVM_HOME=/usr/src/llvm-3.7
export FOREST_HOME=$(pwd)

# test
make test 

# See how it works
cd test/crest/math/ 
forest -verbose -see_each_problem
```

* Tested with llvm-3.7
* Compiled with g++ (Ubuntu 4.8.4-2ubuntu1~14.04.3) 4.8.4

