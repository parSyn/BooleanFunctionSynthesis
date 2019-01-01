#!/bin/bash

#Usage
 
if [ $# -lt 2 ]
then
#./parSyn.sh aigFileName OrderFileName
    echo "Usage ./parSyn.sh AigOrVerilogFileName OrderFileName"
    exit
fi

aigFile=$1
orderFile=$2
export LD_LIBRARY_PATH=$HOME/abc.latest/abc:$HOME/boost_1_68_0/stage/lib:$LD_LIBRARY_PATH
export PATH=$HOME/GitRep/bin:$PATH
numCores=10

mpiexec -np 10 parSyn $aigFile $orderFile 2 $orderFile 0 1 0
