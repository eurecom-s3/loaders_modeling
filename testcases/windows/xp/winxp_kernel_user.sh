#!/bin/bash

git checkout 566e3b2b89e5d63e6e15e26ce2a79c271005a270
git submodule update --recursive

python3 ./generate.py -A models/windows/xp/MiCreateImageFileMap.lmod models/windows/xp/LdrpInitializeProcess.lmod models/windows/generic/return0.lmod models/windows/generic/reasonable_stack.lmod
