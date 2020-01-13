#!/usr/bin/env python

import sys
import logging
import coloredlogs

log = logging.getLogger(__name__)
log.setLevel(10)
coloredlogs.install(level="DEBUG", logger=log)

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
from langlex import tokens
from classes import Variable, Assignment, Expression, Condition, Immediate, ConditionList, ConditionListEntry
from z3_backend import dispatch

import z3

solver = z3.Solver()
variables = {}
conditions = {}

def p_input(p):
    'input : input NEWLINE'
    p[0] = p[1]

def p_input_ass(p):
    'input : assignment_stmt'
    log.debug("Assignment: " + str(p[1]))
    p[1].apply()

def p_input_cond(p):
    'input : condition_stmt'
    log.debug("Condition " + str(p[1]))
    name, condition = p[1]
    conditions[name.upper()] = condition

def p_input_input(p):
    'input : input_stmt'
    log.debug("Input" + str(p[1]))
    variables[p[1].name] = p[1]

def p_input_stmt(p):
    'input_stmt : INPUT VARIABLE NUMBER'
    log.debug("Input statement")
    symb = z3.BitVec(p[2], p[3] * 8)
    var = Variable(p[2], symb)
    p[0] = var

def p_assignment_stmt_uncond(p):
    'assignment_stmt : ASSIGNSTART COLON assignment'
    assignment = p[3]
    p[0] = assignment

def p_assignment_stmt_cond(p):
    'assignment_stmt : ASSIGNSTART conditionlist COLON assignment'
    assignement = p[4]
    assignement.left.symb = assignement.right
    conditionslist = p[2]
    conds = [conditions[c] for c in conditionslist.names]
    assignement.conditions = conds
    p[0] = assignement

def p_condition_stmt_uncond(p):
    'condition_stmt : CONDITIONNAME COLON conditionexpr'
    p[0] = (p[1], p[3])

def p_condition_stmt_cond(p):
    'condition_stmt : CONDITIONNAME conditionlist COLON conditionexpr'
    cond = p[4]
    conditionslist = p[2]
    conds = [conditions[c] for c in conditionslist.names]
    cond.conditions = conds
    p[0] = (p[1], cond)

def p_condition_stmt_noexpr(p):
    'condition_stmt : CONDITIONNAME conditionlist SEMICOLON'
    conditionslist = p[2]
    conds = [conditions[c] for c in conditionslist.names]
    cond = Condition(True, False, conds)
    p[0] = (p[1], cond)

def p_assignment(p):
    'assignment : VARIABLE ARROW expression'
    var = None
    if p[1] not in variables:
        log.debug(f"New variable found {p[1]}")
        var = Variable(p[1])
        variables[var.name] = var
    else:
        var = variables[p[1]]
    p[0] = Assignment(var, p[3])

def p_conditionlist(p):
    '''conditionlist : LPAREN conditionlistint RPAREN'''
    p[0] = p[2]

def p_conditionlistint_1(p):
    'conditionlistint : conditionlistentry'
    p[0] = ConditionList([p[1]])

def p_conditionlistint_2(p):
    'conditionlistint : conditionlistint COMMA conditionlistentry'
    p[0] = p[1] + p[3]

# def p_conditionlistone(p):
#     'conditionlistone : conditionlistentry'
#     p[0] = ConditionList([p[1]])

# def p_conditionlistmulti(p):
#     'conditionlistmulti : | conditionlistentry COMMA conditionlistmulti'
#     p[0] = p[1] + p[3]

# def p_conditionlistmulti(p):
#     'conditionlistmulti : conditionlistentry'
#     p[0] = p[1] + p[3]

def p_conditionlistentry_negcondition(p):
    'conditionlistentry : EXCLAMATION CONDITIONNAME'
    p[0] = ConditionListEntry(p[2], False)

def p_conditionlistentry_condition(p):
    'conditionlistentry : CONDITIONNAME'
    p[0] = ConditionListEntry(p[1], True)

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
    p[0] = Expression(dispatch(p[1], p2))

def p_expression_z3operator2(p):
    'expression : Z3OPERATOR2 expression expression'
    p2 = p[2]
    p3 = p[3]
    p[0] = Expression(dispatch(p[1], p2, p3))

def p_expression_parens(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]

def p_expression_slice(p):
    'expression : expression LBRACKETS expression COMMA expression RBRACKETS'
    p1 = p[1].expr
    p3 = p[3]
    p5 = p[5]
    p[0] = Expression(dispatch('Slice', p1, p3, p5))

def p_expression_indexing(p):
    'expression : expression LBRACKETS expression RBRACKETS'
    p1 = p[1].expr
    p3 = p[3]
    p[0] = Expression(dispatch('Slice', p1, p3))

def p_expression_variable(p):
    'expression : VARIABLE'
    log.debug("Found variable " + p[1])
    varname = p[1]
    if varname not in variables:
        log.critical("Using variable %s before assignement" % varname)
        raise NameError
    p[0] = Expression(variables[varname])

def p_expression_number(p):
    'expression : NUMBER'
    log.debug("Found NUMBER " + str(p[1]))
    p[0] = Immediate(p[1])

def p_expression_string(p):
    'expression : CHAR'
    p[0] = Immediate(p[1])


# Error rule for syntax errors
def p_error(p):
    if p is None:
        return
    log.error("Syntax error in input! %s" % p)

# Build the parser
try:
    parser = yacc.yacc()
except yacc.YaccError as e:
    log.exception(e)
    sys.exit(1)
solver = z3.Solver()

cnt = 0
while True:
    try:
        s = input()
    except EOFError:
        break
    cnt += 1
    if not s: continue
    log.info(f"Line {cnt}: {s}")
    result = parser.parse(s)
    if result:
        print(result)
