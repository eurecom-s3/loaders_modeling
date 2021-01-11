# Language Specifications

## Models
A model is a file (compliant with these specifications) that describes the loading phase of a program, that precedes its launch.  
In general, this process can be divided in a series of stages of two types: parsing stages and validation stages.  
The first stages produce a set of intermediate values starting from the original program.  
These values are then used during the validation stages to enforce soft or hard constraints.
Soft constraints are used to determine which are the following steps of the loading process, while hard constraints are those that abort the entire process tout court in case they are not met.  
Models can be used for two purposes: testcase generation and program validation.  
Testcase generation consists in interpreting the model as a set of SMT constrains. By means of an SMT solver, it is possible to produce sequences of bytes (testcases) that meet all these constraints. If the model is consistent with the loader's behavior, feeding the loader with a testcase will result in the loading phase succeeding.  
Program validation, instead, consists in checking whether a given program respects the constraints enforced by a loader. In other words, the validation process ultimately forecasts whether a program would be successfully loaded by a specific loader or not.

## Core Concepts of the Language
### Structures
Loaders usually cast part of the program headers to well-known data structures, often declared in the C language.  
Our language provides support to C types that can be imported in a model by parsing C header files.
### Immediate Values
Immediate values are either integer (both base10 and base16 numbers are allowed) or single characters. Internally, they are all parsed as integers.
### Variables
Symbolic names given to expressions.
### Expressions
Recursive structures that combine variables, immediate values and other expressions by means of operators.
### Operators Semantics and Arity
| Operator | Arity | Signed | Sized | Meaning | Syntax |
|:--------:|:-----:|:------:|:-----:|:---------------------------------------------:|:--------------------:|
| ADD | 2 | Y | Y | Integer addition |  |
| SUB | 2 | Y | Y | Integer difference |  |
| MUL | 2 | Y | Y | Integer product |  |
| DIV | 2 | Y | Y | Integer division |  |
| UDIV | 2 | N | Y | Integer unsigned division |  |
| MOD | 2 | Y | Y | Integer Modulo |  |
| BITOR | 2 | N | Y | Bitwise OR |  |
| BITAND | 2 | N | Y | Bitwise AND |  |
| BITNOT | 1 | N | Y | Bitwise NOT |  |
| OR | 2 | - | - | Logic OR |  |
| AND | 2 | - | - | Logic AND |  |
| NOT | 1 | - | - | Logic NOT |  |
| EQ | 2 | - | Y | Integer Equality test |  |
| NEQ | 2 | - | Y | Integer Inequality test |  |
| GT/GE | 2 | Y | Y | Integer greater [or equal] comparison |  |
| LT/LE | 2 | Y | Y | Integer less [or equal] comparison |  |
| UGT/UGE | 2 | N | Y | Unsigned greater [or equal] comparison |  |
| ULT/ULE | 2 | N | Y | Unsigned less [or equal] comparison |  |
| ISPOW2 | 1 | N | N | True if &lt;arg&gt; is a power of 2 |  |
| SHL/SHR | 2 | N | Y | Left/Right logic bit-shift | |
| OVFLADD | 2 | - | Y | True if the sum of the two operands produce an overflow | |
| Indexing | 2 | N | Y | Single byte extraction | &lt;var&gt;[byteindex] |
| Slice | 3 | N | Y | Bytevector extraction | &lt;var&gt;[start, nbytes] |

### Syntactic Sugars
|Expression | Meaning | Use case |
|:---------------:|:---------------------------------------:|----------------------------------------------------|
|STRCMP V1 I 'ME' | AND (EQ V1[I] "M") (EQ V1[ADD I 1] "E") | Comparison/Constraints involving printable strings |

## Valid Statements
### INPUT Statements
#### Syntax
`INPUT <variable name> (`<size in bytes>| AS <type>)`  
#### Description
Declare an input variables. For testcase generation, this variable will be completely symbolic, meaning that it could assume any possible values. For program validation, input variables are fed into the process from outside.  
An example of an input variable is the file to produce or validate.  
Input variables must have a fixed size, which can be declared explicitly by adding its size in bytes after its name; or implicitely, by adding a type declaration by means of the `AS` keyword.

### DEFINE Statements
#### Syntax
`DEFINE <constant name> <immediate value>`
#### Description
Syntactic sugar to give names to immediate values. Useful for those that repeats often in a model.  
Interpreted by the frontend parser/preprocessor.

### Soft-Constraints Statements
#### Syntax
`V<number>: <expression>`
#### Description
Introduce a condition that can be later used for conditional statements.  
The value of the condition is defined by the epression on the right side of the statement.

### Validation Statements
#### Syntax (unconditional)
`V<number>: <expression> TERM`
#### Syntax (conditional)
`V<number>(Vn[, Vm[, Vo[...]]]): <expression> TERM`
#### Description
Introduce a hard constraint.  
During program validation, if the constraints is not met, the entire process fails.  
During testcase generation, the list of hard constraints are translated into SMT constraints and then fed to the backend to procude the testcase.
#### Semantics of Conditional Validation
A conditional validation is a hard constraints that behaves in the following way:
1. if the at least one of its prior conditions is not met, its value is TRUE (meaning that the hard constraint is met)  
2. if all its prior constraints are met, its value is defined by its expression  
Conditional hard-constraints
In other words, conditional hard-constraints influence the loading process _only_ if their prior constraints are met.

### Parsing Statements
#### Syntax (unconditional)
`P: <variable name> <- <expression> [AS <type>]`
#### Syntax (conditional)
`P(Vn[, Vm[, Vo[...]]]): <variable name> <- <expression> [AS <type>]`
#### Description
Introduce a parsing stage in the model.  
This roughly corresponds to a variable assignement in procedural languages.  
#### Semantics of Conditional Parsing
A conditional parsing statement roughly corresponds to a variable assignment in a _if-then-else_ statement in procedural languages, with a few caveats.
In the first place, a variable introduced within a conditional statement will have value of 0 if the conditions is not met. The language parser will also produce a warning when this happens, since it could lead to unwanted behaviors.  
If, instead, the output variable of the statement was already defined (i.e., in a previous unconditional parsing statement), and if its conditions are not all met, its value is the one it held before the conditional parsing statement.

### Fixed-increment Loop Statements
#### Syntax (start)
`L<number>: <output> <- LOOP(<input>, <startingoffset>, <structsize>, <count>, <maxunroll>) [AS <type>]`  
`<output>`: variable name  
`<input>`: expression  
`<startingoffset>`: expression  
`<structsize>`: immediate  
`<count>`: expression  
`<maxunroll>`: integer  
#### Syntax (end)
`END L<number>`
#### Description
This statement declares a loop iterating over an array of structures.  
An iteration is made up of all the statements between the start of the loop and its end.  
At the n-th iteration of the loop the output value takes the n-th element of the array.  
The `input` argument is the expression on which to slice upon to extract the elements of the array.  
The `startinoffset` is an expression that indicates the offset (in bytes) at which the array start within the `input` variable.  
`structsize` represents the size (in bytes) of each element of the array. It must be an immediate.  
`count` is an expression representing the number of iterations of the loop.  
`maxunroll` is an integer used _only during testcase generation_ as an upper-bound for `count`. Its role is fundamental due to the lack of loop supports in SMT solvers. In fact, loops in our language are unrolled to overcome this limitation.

### Generic Loop Statements
#### Syntax (start)
`L<number>: <output> <- VLOOP(<start>, <next>, <condition>, <maxunroll>)`
`<output>`: variable name  
`<start>`: expression  
`<next>`: variable name  
`<condition>`: condition name  
`<maxunroll>`: integer  
#### Syntax (end)
`END L<number>`
#### Description
Declares a generic loop to execute the same set of statements multiple times up until a certain condition is met.  
At each iteration the `output` variable takes a different value, according to the following scheme:
1. During the first iteration, its value is set to that of the `start` expression  
2. In the following iteration, its value is set to that of the `next` variable  
The `next` variable must be set inside the body of the loop, by means of a `P` statement.  
`condition` is the identifier of a soft-constraint declared within the body of the loop.  
The semantics of `maxunroll` is the same as for the `fixed-increment loop` statements.  
