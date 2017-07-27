#!/bin/bash 

for a in stall/*
do
	diff $a $1 && echo stall
done

