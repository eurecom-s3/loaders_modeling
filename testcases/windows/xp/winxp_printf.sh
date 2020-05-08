#!/bin/bash

git checkout 44790e0ac5de2569bb583361ba5559a3a89d397c
git submodule update --recursive

ipython -i ./generate.py -- -A models/windows/xp/MiCreateImageFileMap.lmod models/windows/xp/LdrpInitializeProcess.lmod models/windows/generic/printf.lmod models/windows/generic/not_managed.lmod models/windows/generic/reasonable_stack.lmod
