git clone https://github.com/compor/nauseous.git
git clone https://github.com/compor/SNU_NPB.git
cd nauseous
utils/scripts/source_tree/create-symlink-bmk-subdir.sh -h
utils/scripts/source_tree/create-symlink-bmk-subdir.sh -c config/suite_all.txt -s ../SNU_NPB/NPB3.3-SER-C -t . -l src
cd ..
mkdir build-nauseous
cd build-nauseous
../nauseous/utils/scripts/source_tree/build-llvm.sh
cd ../nauseous
git submodule init
git submodule update
cd -
../nauseous/utils/scripts/source_tree/build-llvm.sh
make -j4
