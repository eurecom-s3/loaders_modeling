import logging
import ply.lex as lex
import re
from enum import Enum, auto, unique

from ..classes import Base, Optimizations

log = logging.getLogger(__name__)
log.setLevel(logging.NOTSET)


class Lexer:
    tokens = (
        'NEWLINE',

        # these translate to z3 functions
        'OPERATOR1',
        'OPERATOR2',

        # string comparison - a syntactic sugar
        'STRCMP',

        'ASSIGNSTART',
        'CONDITIONNAME',
        'GENCONDITIONNAME',
        'LOOPSTART',
        'LOOPEND',
        'LOOP',
        'VLOOP',
        'DBG',
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
        'STR',
        'BOOL',
        'VARIABLE',
        'INPUT',
        'OUTPUT',

        'LOADTYPES',
        'TYPE',
        'SIZEOF',
        'DEFINE',

        'FROMFILE',
        'OPTIMIZE',
    )

    def t_OPERATOR1(self, t):
        r'(NOT|Not|BITNOT|BITNot|BitNot|ISPOW2|IsPow2|isPow2|Setc|SECT|NSect|NSECT|OptHdr|OPTHDR)'
        t.value = t.value.upper()
        log.debug("OPERATOR1 token")
        return t

    def t_OPERATOR2(self, t):
        r"(ADD|SUB|DIV|UDIV|AND|OR|ULE|UGE|ULT|UGT|Add|Sub|Div|UDiv|And|Or|ULe|UGe|ULt|UGt|BITAND|BITAnd|BitAnd|BITOR|BITOr|BitOr|LE|Le|GE|Ge|NEQ|NEq|Neq|EQ|Eq|LT|Lt|GT|Gt|INT|Int|MOD|Mod|MUL|Mul|ALIGNUP|ALIGNDOWN|ISALIGNED|SHR|ShR|SHL|ShL|OVFLADD|OVFLAdd|OvflAdd)\s"
        log.debug("OPERATOR2 token")
        t.value = t.value[:-1].upper()
        return t

    def t_STRCMP(self, t):
        r"(STRCMP|STRCmp|StrCmp)"
        t.value = t.value[:-1].upper()
        return t

    def t_CHAR(self, t):
        r'"[^"]"'
        t.value = ord(t.value[1])
        log.debug("A single char value token")
        return t

    def t_STR(self, t):
        r"'[^']+'"
        t.value = eval('"' + t.value[1:-1] + '"')
        return t

    def t_BOOL(self, t):
        r"(TRUE|True|true|FALSE|False|false)"
        val = t.value.upper()
        t.value = True if val == "TRUE" else False
        log.debug(f"Found immediate boolean value {val}")
        return t

    def t_TERMINATOR(self, t):
        r"term"
        log.debug("Terminal condition token")
        return t

    t_LBRACKETS   = r'\['
    t_RBRACKETS   = r'\]'
    t_LPAREN      = r'\('
    t_RPAREN      = r'\)'
    t_ARROW       = r'<-'
    t_SEMICOLON   = r';'
    t_EXCLAMATION = r'!'
    t_DOT         = r'\.'
    t_COMMA       = r','
    t_NEWLINE     = r'\n'

    def t_COLON(self, t):
        r':'
        return t

    def t_INPUT(self, t):
        r'^(INPUT|input)'
        log.debug("Input variable token")
        return t

    def t_OUTPUT(self, t):
        r'^(OUTPUT|output)'
        log.debug("Output variable token")
        return t

    def t_ASSIGNSTART(self, t):
        r'(P|p)(?=(:|\())'
        log.debug("Assignement start token")
        t.value = t.value.lstrip()
        return t

    def t_LOOPSTART(self, t):
        r'(L|l)\d+(?=(:|\())'
        log.debug("Loop start token")
        v = t.value.lstrip()
        v = int(v[1:])
        t.value = v
        return t

    def t_DBG(self, t):
        r'(D|d)(?=(:|\())'
        log.debug("Debug token")
        t.value = t.value.lstrip()
        return t

    def t_LOOPEND(self, t):
        r'(END|End|end)\s(L|l)\d+'
        log.debug("Loop end token")
        v = t.value.lstrip()
        v = int(v[5:])
        t.value = v
        return t

    def t_LOOP(self, t):
        r'LOOP'
        return t

    def t_VLOOP(self, t):
        r'VLOOP'
        return t

    def t_CONDITIONNAME(self, t):
        r'(V|v)\d+'
        log.debug("Condition name token")
        return t

    def t_GENCONDITIONNAME(self, t):
        r'(G|g)\d+'
        log.debug("Condition name token")
        return t

    def t_LOADTYPES(self, t):
        r'(LOAD|Load|load)(REL|Rel|rel)?\s'
        if 'rel' in t.value.lower():
            t.value = True
        else:
            t.value = False
        return t

    def t_TYPE(self, t):
        r'(AS|As|as)\s'
        return t

    def t_SIZEOF(self, t):
        r'(SIZEOF|SizeOf|sizeof)\s'
        return t

    def t_DEFINE(self, t):
        r'(DEFINE|Define|define)\s'
        return t

    def t_FROMFILE(self, t):
        r'FROMFILE\s'
        return t

    def t_OPTIMIZE(self, t):
        r'(MAXIMIZE|MINIMIZE)'
        if 'MAX' in t.value:
            t.value = Optimizations.MAXIMIZE
        else:
            t.value = Optimizations.MINIMIZE
        return t

    def t_VARIABLE(self, t):
        r"[a-zA-Z_][a-zA-Z_0-9]+"
        return t

    # A regular expression rule with some action code
    def t_NUMBER(self, t):
        r'(0(x|X)[a-fA-F0-9]+|\d+)'
        log.debug("Number token")
        try:
            t.value = int(t.value)
        except ValueError:
            t.value = int(t.value, 16)
        return t

    t_ignore_comments = r'\#.*'

    # Define a rule so we can track line numbers
    def t_newline(self, t):
        r'\n+'
        log.debug("New line found")
        t.lexer.lineno += len(t.value)

    # A string containing ignored characters (spaces and tabs)
    t_ignore  = ' \t'

    # Error handling rule
    def t_error(self, t):
        print("Illegal character '%s'" % t.value[0])
        t.lexer.skip(1)

    def __init__(self):
        # Build the lexer
        lexer = lex.lex(module=self)
