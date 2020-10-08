#!/bin/bash

cat $1 $2 | grep -v "Succe" | awk -F ' ' '{print $1}' | sort | uniq > $3
