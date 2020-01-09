import logging
import ply.lex as lex
import re

import z3

from classes import Base

log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)


tokens = (
    'NEWLINE',

    # these translate to z3 functions
    'Z3OPERATOR1',
    'Z3OPERATOR2',

    'ASSIGNSTART',
    'CONDITIONNAME',
#    'CONDITION',
    'COMMA',
    'COLON',
    'TERMINATOR',

    # slicing
    'LBRACKETS',
    'RBRACKETS',

    # parentheses
    'LPAREN',
    'RPAREN',

    # ->
    'ARROW',

    # #
    'COMMENT',

    'NUMBER',
    'CHAR',
    'VARIABLE',
    'INPUT'
)

def t_Z3OPERATOR1(t):
    r'(NOT|Not)'
    t.value = t.value.upper()
    log.debug("OPERATOR1 token")
    return t

def t_Z3OPERATOR2(t):
    r"(ADD|SUB|UDIV|AND|OR|ULE|Add|Sub|UDiv|And|Or|ULe|BITAND|BITAnd|BitAnd|BITOR|BITOr|BitOr|GE|Ge|NEQ|NEq|EQ|Eq)"
    log.debug("OPERATOR2 token")
    t.value = t.value.upper()
    return t

def t_CHAR(t):
    r'"[^"]"'
    t.value = ord(t.value[1])
    log.debug("A single char value token")
    return t

def t_TERMINATOR(t):
    r"term"
    log.debug("Terminal condition token")
    return t

t_LBRACKETS  = r'\['
t_RBRACKETS  = r'\]'
t_LPAREN     = r'\('
t_RPAREN     = r'\)'
t_ARROW      = r'<-'
t_COLON      = r':'
t_COMMA      = r','
t_NEWLINE    = r'\n'

def t_INPUT(t):
    r'(INPUT|input)'
    log.debug("Input variable token")
    return t

def t_ASSIGNSTART(t):
    r'(P|p)'
    log.debug("Assignement start token")
    return t

def t_CONDITIONNAME(t):
    r'(V|v)\d+'
    log.debug("Condition name token")
    return t

#t_CONDITION      = r'v\d+'

t_VARIABLE   = "[a-zA-Z_]+"

# A regular expression rule with some action code
def t_NUMBER(t):
    r'(0(x|X)[a-fA-F0-9]+|\d+)'
    log.debug("Number token")
    try:
        t.value = int(t.value)
    except ValueError:
        t.value = int(t.value, 16)
    return t

t_ignore_comments = r'\#.*'

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    log.debug("New line found")
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()
