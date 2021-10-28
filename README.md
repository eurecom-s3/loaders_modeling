# What is this about?

The objective of this project is to provide a framework for modeling and analyzing the behavior of parsers for executable file formats, like the ones we can find in operating system loaders and reverse engineering tools.  

# What do I find in this repo?

This project ships some ready-to-use models as well as the code of the analysis framework.  
The models can be found in the dedicated [submodule](models), while the code of the interpreter for the custom language is in [modelLang](modelLang) directory.  

# Modeling Language

The first step in the analysis consists in writing a "model" of the parser using the custom language supported by the framework.  
Here follows an example extracted from the models of the Windows loader.
```
INPUT HEADER 2048 as DOSHeader

## Check the MZ magic number
V1: AND EQ HEADER.magic[0] "M" EQ HEADER.magic[1] "Z" term
V2: ULE (ADD HEADER.e_lfanew 0xf8) FILESIZE term

P: NT_HEADER <- HEADER[HEADER.e_lfanew, sizeof _IMAGE_NT_HEADERS] as _IMAGE_NT_HEADERS
## Check the PE magic number
V3: EQ NT_HEADER.Signature 0x4550  term

```
For more information about the modeling language, check out [SPECIFICATIONS.md](SPECIFICATIONS.md) and [EXAMPLE.md](EXAMPLE.md).  

# Analysis Tasks & Examples

## Sample validation
Given an executable and the model of a parser as input, the framework can determine whether the first respects the constraints of the second, in other words, whether the modeled software considers the input file as a valid executable.
To check whether an executable respects the constraints of a model, you can run:  
```
python3 verify.py <model file> <sample>
```
For example, if you want to check whether an unknown sample can run under Windows 10 by using the ready-to-use models in this project, you can launch:  
```
python3 verify.py models/windows/10/MiCreateImageFile.lmod path/to/the/sample
```
The script returns 0 if the executable is valid, or 1 otherwise (in this case, the scripts prints also one line pointing to the broken constraint in the model).

## Sample generation
The framework can create program headers that are valid according to one or more models.
The logic for the generating valid samples is implemented in the `generate.py` script, which can be invoked as follows:
```
python3 generate.py -A <model 1> [<model 2> [<model 3> ... ]]
```
For example, to generate a valid test case for Windows 7, you can run the following command that combines the models of both the kernel-space and user-space portions of its loader:
```
python3 generate.py -A models/windows/7/MiCreateImageFile.lmod models/windows/7/LdrpInitializeProcess.lmod
```
The output file can be specified with the `-O` flag (default: `testcase`).

## Differential test case generation
Given two or more models, the framework can create program headers that are valid according to a subset of them, but invalid for the others.
`generate.py` implements also the differential test case generation, and can be invoked with:
```
python3 generate.py -A <model 1> [<model 2> [...]] -N <model 3> [<model 3> [...]]
```
To generate a sample that runs in Windows 7 but not in Windows 10, you can execute:  
```
./generate.py -A models/windows/10/MiCreateImageFileMap.lmod models/windows/10/LdrpInitializeProcess.lmod -N models/windows/7/MiCreateImageFileMap.lmod models/windows/7/LdrpInitializeProcess.lmod
```

## Differences enumeration
Given two models, the framework is able to create many different differential test cases, exploiting different discrepancies among the two models.  

The `differential.py` script implements the logic for the differences enumeration technique and can be invoked the same way as `generate.py`.

## Corner cases generation
Given a model, the framework creates many test cases that cover all the possible configurations that a set of models consider valid.  
This technique is implemented in the `explore_condition.py` script, which can run with the following command:  
```
python3 explore_conditions.py -M <model 1> [<model 2> [...]]
```

# Setup/Installation

The best way to start using this project is by creating a virtual environment.  
```
mkvirtualenv --python=python3 models
```
This project uses python3-specific features and as such is unlikely to work with python2.  
Most of the project dependencies can be installed using pip:
```
pip install -r requirements.txt
```
The `z3` solver needs to be installed separatedly. On Ubuntu 20.04, you can do that with:
```
sudo apt install z3
```

# Publications and Conference Talks

This work has been published at the [24th International Symposium on Research in Attacks, Intrusions and Defenses (RAID 2021)](https://raid2021.org/).  
You can read the paper [here](https://www.eurecom.fr/publication/6603/download/sec-publi-6603.pdf).  
If you want to cite this work in your academic paper, you can use this:

```
@inproceedings{10.1145/3471621.3471848,
  author = {Nisi, Dario and Graziano, Mariano and Fratantonio, Yanick and Balzarotti, Davide},
  title = {Lost in the Loader:The Many Faces of the Windows PE File Format},
  year = {2021},
  publisher = {Association for Computing Machinery},
  booktitle = {24th International Symposium on Research in Attacks, Intrusions and Defenses},
  location = {San Sebastian, Spain},
  series = {RAID '21}
}
```
We will also present this project at [Black Hat Europe 2021](https://www.blackhat.com/eu-21/).
