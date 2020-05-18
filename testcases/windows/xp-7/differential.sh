#!/bin/bash

git checkout e13f7b46e1a9b1c1f0c5f5648f0d2910904d3b7d
git submodule update --recursive

ipython -i ./differential.py -- -A models/windows/xp/MiCreateImageFileMap.lmod models/windows/xp/LdrpInitializeProcess.lmod models/windows/generic/not_managed.lmod models/windows/generic/return0.lmod models/windows/generic/reasonable_stack.lmod -N models/windows/7/MiCreateImageFileMap.lmod -O xp-7/testcase
