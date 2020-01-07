#!/usr/bin/env python

import logging
import coloredlogs

log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)
coloredlogs.install(level='DEBUG', logger=log)

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
from langlex import tokens, z3_funcs
from classes import Variable, Assignment, Expression, Condition

import z3

solver = z3.Solver()
variables = {}

def p_input(p):
    'input : input NEWLINE'
    p[0] = p[1]

def p_input_ass(p):
    'input : assignment_stmt'
    log.debug("Assignment statement found")
    print("Assignment", p[1])

def p_input_cond(p):
    'input : condition_stmt'
    log.debug("Condition statement found")
    print("Condition", p[1])

def p_input_input(p):
    'input : input_stmt'
    log.debug("Input statement found")
    print("Input", p[1])
    variables[p[1].name] = p[1]

def p_input_stmt(p):
    'input_stmt : INPUT VARIABLE NUMBER'
    log.debug("Input statement")
    var = Variable(p[2], p[3])
    p[0] = var

def p_assignment_stmt_uncond(p):
    'assignment_stmt : ASSIGNSTART COLON assignment'
    p[0] = p[1:]

def p_assignment_stmt_cond(p):
    'assignment_stmt : ASSIGNSTART conditionlist COLON assignment'
    p[0] = p[1:]

def p_condition_stmt_uncond(p):
    'condition_stmt : CONDITIONNAME COLON conditionexpr'
    p[0] = p[1:]

def p_condition_stmt_cond(p):
    'condition_stmt : CONDITIONNAME conditionlist COLON conditionexpr'
    p[0] = p[1:]

def p_assignment(p):
    'assignment : VARIABLE ARROW expression'
    var = None
    if p[1] not in variables:
        var = Variable(p[1])
        variables[var.name] = var
    else:
        var = variables[p[1]]
    p[0] = Assignment(var, p[3])

def p_conditionlist(p):
    'conditionlist : CONDITIONNAME COMMA conditionlist'
    p[0] = [p[1], *p[3]]

def p_conditionlist_paren(p):
    'conditionlist : LPAREN conditionlist RPAREN'
    p[0] = p[2]

def p_conditionlist_condition(p):
    'conditionlist : CONDITIONNAME'
    p[0] = [p[1]]

def p_condition_terminal(p):
    'conditionexpr : expression TERMINATOR'
    p[0] = Condition(p[1], True)

def p_condition_normal(p):
    'conditionexpr : expression'
    p[0] = Condition(p[1], False)

def p_expression_z3operator1(p):
    'expression : Z3OPERATOR1 expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p[0] = Expression(p[1](p2))

def p_expression_z3operator2(p):
    'expression : Z3OPERATOR2 expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p[1](p2, p3))

def p_expression_eq(p):
    'expression : EQ expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p2 == p3)

def p_expression_neq(p):
    'expression : NEQ expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p2 != p3)

def p_expression_ge(p):
    'expression : GE expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p2 >= p3)

def p_expression_bitor(p):
    'expression : BITOR expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p2 | p3)

def p_expression_bitand(p):
    'expression : BITAND expression expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p3 = p[3].expr
    p[0] = Expression(p2 & p3)

def p_expression_bitnot(p):
    'expression : BITNOT expression'
    p2 = p[2].expr
    if isinstance(p2, Variable):
        p2 = p2.symb
    p[0] = Expression(~p2)

def p_expression_parens(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]

def p_expression_slice(p):
    'expression : expression LBRACKETS NUMBER COMMA NUMBER RBRACKETS'
    p1 = p[1].expr
    p3 = p[3]
    p5 = p[5]
    p[0] = Expression(z3_funcs['Slice'](p1, p3, p5))

def p_expression_indexing(p):
    'expression : expression LBRACKETS NUMBER RBRACKETS'
    p1 = p[1].expr
    p3 = p[3]
    p[0] = Expression(z3_funcs['Slice'](p1, p3))

def p_expression_variable(p):
    'expression : VARIABLE'
    print("Found variable", p[1])
    varname = p[1]
    if varname not in variables:
        log.error("Using variable %s before assignement" % varname)
        raise NameError
    p[0] = Expression(variables[varname])

def p_expression_number(p):
    'expression : NUMBER'
    print("Found NUMBER", p)
    p[0] = Expression(p[1])

def p_expression_string(p):
    'expression : CHAR'
    p[0] = Expression(p[1])


# Error rule for syntax errors
def p_error(p):
    if p is None:
        return
    print("Syntax error in input! %s" % p)

# Build the parser
parser = yacc.yacc()

while True:
    try:
        s = input()
    except EOFError:
        break
    if not s: continue
    log.info("Line: %s" % s)
    result = parser.parse(s)
    if result:
        print(result)
