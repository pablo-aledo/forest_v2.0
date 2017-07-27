## Typical installation:

```
# needed dependencies
sudo apt-get install sqlite3 graphviz meld

# z3 (if doesnt work, go to http://z3.codeplex.com/SourceControl/latest#README, download and follow the instructions)
git clone https://git01.codeplex.com/z3
cd z3-*
./configure
python scripts/mk_make.py
cd build
make
sudo make install

# add a link to your llvm-installation path in /llvm-2.9/
sudo ln -s <your-llvm-path> /llvm-2.9

# compile
make 

# add bin to path
export PATH=$(pwd)/bin/:$PATH

# test
make test 

# See how it works
cd test/crest/math/ 
forest -verbose -see_each_problem
```

* Tested with llvm-2.9
* Compiled with gcc-4.7.2
