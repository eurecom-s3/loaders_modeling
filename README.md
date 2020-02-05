# Important: Use dev branch for any changes

# Setup
The best way to start using this project is by creating a virtual environment.  
Supposing you have installed the virtualenv wrappers, you can do it by typing `mkvirtualenv --python=python3 models`.  
Note that this is `python3` project. If you are still using `python2` (which you should not anymore), most likely this project is not gonna work.

## Dependencies
From within your virtual environment, you can install the dependencies with: `pip install -r requirements.txt`

# Code description
The `check_model.py` script is the entry point of the project.  
It should be run from within the root directory of the project.  
Most likely you want to run it in IPython, so to have an interactive shell after it finishes to create and check the model.  
You can do this with `ipython -i check_model.py <path to the model>`.  
The `classes.py` script contains the definition of the IR.  
`utils.py` contains a collection of methods and classes commonly used in the rest of the code.

## Directory structure
- parsers: the code for parsing the language and produce the IR
- backends: the code for different interpreters of the IR. For now only z3 is supported (using pyz3 wrappers)
- structures: mostly adapted from `angr`; here is the logic to parse C structures
  - headers: the directory in which the parser looks for C header to use in models
- tests: very basic functional tests
