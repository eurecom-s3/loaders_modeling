#!/bin/bash

git checkout 5e61eef93ee6031e3854b5c3bede96891b292ec9
git submodule update --recursive

ipython -i ./generate.py -- -A models/windows/7/MiCreateImageFileMap.lmod models/windows/7/LdrpInitializeProcess.lmod  models/windows/generic/reasonable_stack.lmod models/windows/generic/printf_import.lmod
