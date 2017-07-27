#!/bin/bash

[ "`uname -m | grep 64`" ] || ( echo "This version is meant to be run in a x86_64 machine." ); [ "`uname -m | grep 64`" ] || exit;
[ "`which g++`" ] || ( echo "This program needs g++ installed (tested with Ubuntu 4.8.2-19ubuntu1)." ); [ "`which g++`" ] ||  exit;

rm -rf forest*
wget teisa.unican.es/forest/images/forest_svcomp_16.tar.gz -O - | tar -xz
cd forest

export PATH=`pwd`/bin:$PATH
export LD_LIBRARY_PATH=`pwd`/lib:$LD_LIBRARY_PATH
export FOREST_HOME=`pwd`
export LLVM_HOME=`pwd`/tools/llvm-2.9
export CPACHECKER_HOME=`pwd`/tools/CPAchecker-1.3.4-unix
export CSEQ_HOME=`pwd`/tools/cseq-2.0b

reset
rm -rf debug_output
echo '===== Packages =====' >> debug_output 2>> debug_output
dpkg --get-selections >> debug_output 2>> debug_output
dpkg -l >> debug_output 2>> debug_output
echo '===== Distribution =====' >> debug_output 2>> debug_output
uname -a >> debug_output 2>> debug_output
lsb_release -a >> debug_output 2>> debug_output
cat /etc/issue >> debug_output 2>> debug_output
echo '===== Versions =====' >> debug_output 2>> debug_output
gcc --version >> debug_output 2>> debug_output
g++ --version >> debug_output 2>> debug_output
python --version >> debug_output 2>> debug_output
llc --version >> debug_output 2>> debug_output
llvm-gcc --version >> debug_output 2>> debug_output
opt --version >> debug_output 2>> debug_output
sqlite3 --version >> debug_output 2>> debug_output
z3 -version >> debug_output 2>> debug_output
./tools/cseq-2.0b/cseq.py --version >> debug_output 2>> debug_output
echo '===== libraries =====' >> debug_output 2>> debug_output
ls /lib/x86_64-linux-gnu >> debug_output 2>> debug_output
ls /lib64 >> debug_output 2>> debug_output
echo '===== mounts =====' >> debug_output 2>> debug_output
mount >> debug_output 2>> debug_output
echo "tmpdir = " $TMPDIR >> debug_output 2>> debug_output
echo '===== ./test/svcomp_16/3-Concurrency/bigshot_p_false =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/3-Concurrency/bigshot_p_false; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/3-Concurrency/bigshot_p_false; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/3-Concurrency/01_inc_true =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/3-Concurrency/01_inc_true; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/3-Concurrency/01_inc_true; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/4-Loops/functions_false-unreach-call1 =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/4-Loops/functions_false-unreach-call1; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/4-Loops/functions_false-unreach-call1; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/4-Loops/count_up_down_true-unreach-call_true-termination =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/4-Loops/count_up_down_true-unreach-call_true-termination; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/4-Loops/count_up_down_true-unreach-call_true-termination; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/8-Recursive/recHanoi01_true-unreach-call_true-termination =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/8-Recursive/recHanoi01_true-unreach-call_true-termination; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/8-Recursive/recHanoi01_true-unreach-call_true-termination; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/8-Recursive/id_o20_false-unreach-call =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/8-Recursive/id_o20_false-unreach-call; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/8-Recursive/id_o20_false-unreach-call; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/1-Arrays/data_structures_set_multi_proc_trivial_true-unreach-call_ground =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/1-Arrays/data_structures_set_multi_proc_trivial_true-unreach-call_ground; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/1-Arrays/data_structures_set_multi_proc_trivial_true-unreach-call_ground; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/7-MemSafety/java_BubbleSort_unsafe_false-valid-deref =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/7-MemSafety/java_BubbleSort_unsafe_false-valid-deref; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/7-MemSafety/java_BubbleSort_unsafe_false-valid-deref; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output
echo '===== ./test/svcomp_16/7-MemSafety/openbsd_cbzero-alloca_true-valid-memsafety =====' >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/7-MemSafety/openbsd_cbzero-alloca_true-valid-memsafety; forest -show_frontier >> $FOREST_HOME/debug_output
cd $FOREST_HOME/test/svcomp_16/7-MemSafety/openbsd_cbzero-alloca_true-valid-memsafety; forest -verbose 2>&1 | head -n 1000 >> $FOREST_HOME/debug_output

