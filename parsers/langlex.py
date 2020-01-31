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
    'CONDITIONSTART',
    'CONDITIONNAME',
    'LOOPSTART',
    'LOOPEND',
    'LOOP',
    'COMMA',
    'COLON',
    'SEMICOLON',
    'EXCLAMATION',
    'DOT',
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
    'BOOL',
    'VARIABLE',
    'INPUT',

    'LOADTYPES',
    'TYPE',
    'SIZEOF'
)

def t_Z3OPERATOR1(t):
    r'(NOT|Not|BITNOT|BITNot|BitNot|ISPOW2|IsPow2|isPow2)'
    t.value = t.value.upper()
    log.debug("OPERATOR1 token")
    return t

def t_Z3OPERATOR2(t):
    r"(ADD|SUB|DIV|UDIV|AND|OR|ULE|UGE|ULT|UGT|Add|Sub|Div|UDiv|And|Or|ULe|UGe|ULt|UGt|BITAND|BITAnd|BitAnd|BITOR|BITOr|BitOr|LE|Le|GE|Ge|NEQ|NEq|EQ|Eq|LT|Lt|GT|Gt|INT|Int|MOD|Mod|MUL|Mul)\s"
    log.debug("OPERATOR2 token")
    t.value = t.value[:-1].upper()
    return t

def t_CHAR(t):
    r'"[^"]"'
    t.value = ord(t.value[1])
    log.debug("A single char value token")
    return t

def t_BOOL(t):
    r"(TRUE|True|true|FALSE|False|false)"
    val = t.value.upper()
    t.value = True if val == "TRUE" else False
    log.debug(f"Found immediate boolean value {val}")
    return t

def t_TERMINATOR(t):
    r"term"
    log.debug("Terminal condition token")
    return t

t_LBRACKETS   = r'\['
t_RBRACKETS   = r'\]'
t_LPAREN      = r'\('
t_RPAREN      = r'\)'
t_ARROW       = r'<-'
t_COLON       = r':'
t_SEMICOLON   = r';'
t_EXCLAMATION = r'!'
t_DOT         = r'\.'
t_COMMA       = r','
t_NEWLINE     = r'\n'

def t_INPUT(t):
    r'(INPUT|input)\s'
    log.debug("Input variable token")
    return t

def t_ASSIGNSTART(t):
    r'^(    )*(P|p)'
    log.debug("Assignement start token")
    t.value = t.value.lstrip()
    return t

def t_LOOPSTART(t):
    r'^\s*(L|l)\d+'
    log.debug("Loop start token")
    v = t.value.lstrip()
    v = int(v[1:])
    t.value = v
    return t

def t_LOOPEND(t):
    r'^(    )*(END|End|end)\s+(L|l)\d+'
    log.debug("Loop end token")
    v = t.value.lstrip()
    v = int(v[5:])
    t.value = v
    return t

def t_LOOP(t):
    r'LOOP'
    return t

def t_CONDITIONNAME(t):
    r'(V|v)\d+'
    log.debug("Condition name token")
    return t

def t_LOADTYPES(t):
    r'(LOAD|Load|load)\s'
    return t

def t_TYPE(t):
    r'(AS|As|as)\s'
    return t

def t_SIZEOF(t):
    r'(SIZEOF|SizeOf|sizeof)\s'
    return t

def t_VARIABLE(t):
    r"[a-zA-Z_]+"
    return t

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
