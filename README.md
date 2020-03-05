# Setup
The best way to start using this project is by creating a virtual environment.  
Supposing you have installed the virtualenv wrappers, you can do it by typing `mkvirtualenv --python=python3 models`.  
Note that this is a `python3` project. If you are still using `python2` (which you should not anymore), most likely this project is not gonna work.

## Dependencies
From within your virtual environment, you can install the dependencies with: `pip install -r requirements.txt`

# Usage  
## generate.py  
The `generate.py` script produce a test-case that complies to the rules given in input.  
The script takes two lists of models. The first list, that starts with the `--assert` flag, is made of by the models whose conditions must be asserted in the test-case. This list must contain at least one model file.  
The second (and optional) list, tagged with `--negates`, contains those models that the test-case must disown.  
In other words, the test-case produced complies with all the models in the `assert` list, but with none of those in the `negates` list.  

## verify.py  
`verify.py` takes a model and a file as input and tells whether the file respects the constraints in the model (`verification`).  

## Generics
Both scripts should be run from within the root directory of the project.  
For debugging purposes, it is helpful to run them in IPython, so to have an interactive shell after the scripts finish.  
You can do this with `ipython -i (verify|generate).py -- <arguments>`.  

# Directory structure
- parsers: the code for parsing the language and produce the IR  
- backends: the code for different interpreters of the IR. Supported backends are:  
  - z3 (by means of the pyz3 wrappers), for both test-case generation and validation  
  - python, only for validation  
- structures: mostly adapted from `angr`; here is the logic to parse C structures  
  - headers: the directory in which the parser looks for C header to use in models  
- tests: very basic functional tests  
- models: sub-module containing the models of the loader of different OSs  
