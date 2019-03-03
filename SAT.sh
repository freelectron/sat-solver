#!/usr/bin/env bash

#S = $1
#path = $2

echo "You would like to run heuristic nr $1"
echo "Path to the input file is $2"

python SAT.py $1 $2
