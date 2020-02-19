# Important: Use dev branch for any changes

# Setup
The best way to start using this project is by creating a virtual environment.  
Supposing you have installed the virtualenv wrappers, you can do it by typing `mkvirtualenv --python=python3 models`.  
Note that this is a `python3` project. If you are still using `python2` (which you should not anymore), most likely this project is not gonna work.

## Dependencies
From within your virtual environment, you can install the dependencies with: `pip install -r requirements.txt`

# Code description
The project has two entry points: `verify.py` and `generate.py`.  
`verify.py` takes a model and a file as input and tells whether the file respects the constraints in the model (`verification`).  
The `generate.py` script takes a model as input and create a test-case that satisfies the model constraints.  
Both scripts should be run from within the root directory of the project.  
For debugging purposes, it is helpful to run them in IPython, so to have an interactive shell after the scripts finish.  
You can do this with `ipython -i (verify|generate).py <path to the model> [path to the file]`.  
The `classes.py` script contains the definition of the IR.  
`utils.py` contains a collection of methods and classes commonly used in the rest of the code.

## Directory structure
- parsers: the code for parsing the language and produce the IR  
- backends: the code for different interpreters of the IR. Supported backends are:  
  - z3 (by means of the pyz3 wrappers), for both test-case generation and validation  
  - python, only for validation  
- structures: mostly adapted from `angr`; here is the logic to parse C structures  
  - headers: the directory in which the parser looks for C header to use in models  
- tests: very basic functional tests  
