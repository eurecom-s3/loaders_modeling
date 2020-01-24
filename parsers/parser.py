import sys
import logging
import pickle
from collections import deque, defaultdict
from utils import customdefdict

import coloredlogs

log = logging.getLogger(__name__)
log.setLevel(10)
coloredlogs.install(level="DEBUG", logger=log)

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
from .langlex import tokens
from classes import Variable, Assignment, Expression, Condition, Immediate, BoolImmediate, ConditionList, ConditionListEntry, Loop, Input
from backends import dispatch

variables = customdefdict(lambda x: Variable(x))
conditions = {}
block_stack = deque()
input_name = None

statements = []
loaded_types = {}

def p_input(p):
    'input : input NEWLINE'
    p[0] = p[1]

def p_input_ass(p):
    'input : assignment_stmt'
    log.debug("Assignment: " + str(p[1]))
    if len(block_stack) == 0:
        statements.append(p[1])
    else:
        block = block_stack.pop()
        block.add_statement(p[1])
        block_stack.append(block)

def p_input_cond(p):
    'input : condition_stmt'
    log.debug("Condition " + str(p[1]))
    name, condition = p[1]
    conditions[name.upper()] = condition
    condition.name = name.upper()
    if len(block_stack) == 0:
        statements.append(condition)
    else:
        block = block_stack.pop()
        block.add_statement(condition)
        block_stack.append(block)

def p_input_input(p):
    'input : input_stmt'
    log.debug("Input " + str(p[1]))
    stmt = Input(p[1][0], p[1][1])
    statements.append(stmt)
    variables[p[1][0].name] = p[1][0]

def p_input_loopstart(p):
    'input : loopstart_stmt'
    log.debug("Loop start " + str(p[1]))
    loop = p[1][1]
    block_stack.append(loop)
    var = variables[loop.output_name]
    input_var = loop.input_var

def p_input_loopend(p):
    'input : loopend_stmt'
    loop = block_stack.pop()
    if loop._loop_name != p[1][0]:
        log.critical("Loop end does not match current loop name")
        raise ValueError
    log.debug("Loop end " + str(p[1][0]))
    statements.append(loop)

def p_input_load(p):
    'input : load_stmt'
    os = p[1][1]
    header = p[1][0]
    module_name = 'structures.' + (os if os != "DEFAULT" else "cparser")
    module = __import__(module_name, globals(), locals(), ['parse_file'])
    with open(f"structures/headers/{header}.h", "r") as fp:
        new_types = module.parse_file(fp.read())
    log.debug(f"Loaded {len(new_types[1])} new types.")
    loaded_types.update(new_types[1])

def p_load_stmt(p):
    'load_stmt : LOADTYPES VARIABLE VARIABLE'
    p[0] = (p[2], p[3])

def p_load_stmt_2(p):
    'load_stmt : LOADTYPES VARIABLE'
    p[0] = (p[2], "DEFAULT")

def p_input_stmt_type(p):
    'input_stmt : INPUT VARIABLE NUMBER TYPE VARIABLE'
    log.debug("Input statement")
    t = p[5]
    if t not in loaded_types:
        log.warning(f"Unknown type {t}. Defaulting to untyped variable")
        var = (Variable(p[2]), p[3])
    else:
        var = (Variable(p[2], loaded_types[t]), p[3])
    p[0] = var

def p_input_stmt(p):
    'input_stmt : INPUT VARIABLE NUMBER'
    log.debug("Input statement")
    var = (Variable(p[2]), p[3])
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
    conds = [~conditions[c.name] if c.negated else conditions[c.name]
             for c in conditionslist]
    assignement.conditions = conds
    p[0] = assignement

def p_condition_stmt_uncond(p):
    'condition_stmt : CONDITIONSTART COLON conditionexpr'
    p[3].name = p[1]
    p[0] = (p[1], p[3])

def p_condition_stmt_cond(p):
    'condition_stmt : CONDITIONSTART conditionlist COLON conditionexpr'
    cond = p[4]
    cond.name = p[1]
    conditionslist = p[2]
    conds = [conditions[c] for c in conditionslist.names]
    cond.conditions = conds
    p[0] = (p[1], cond)

def p_condition_stmt_noexpr(p):
    'condition_stmt : CONDITIONSTART conditionlist SEMICOLON'
    conditionslist = p[2]
    conds = [conditions[c] for c in conditionslist.names]
    cond = Condition(True, False, conds)
    p[0] = (p[1], cond)


def p_loopstart_stmt(p):
    'loopstart_stmt : LOOPSTART COLON VARIABLE ARROW LOOP LPAREN expression COMMA expression COMMA NUMBER COMMA expression COMMA NUMBER RPAREN'
    loopindex = p[1]
    loop = Loop(p[1], p[3], p[7], p[9], p[11], p[13], p[15])
    p[0] = (loopindex, loop)

def p_loopend_stmt(p):
    'loopend_stmt : LOOPEND'
    p[0] = (p[1], )

def p_assignment_typed(p):
    'assignment : VARIABLE ARROW expression TYPE VARIABLE'
    var = None
    t = p[5]
    if t not in loaded_types:
        log.warning(f"Unknown type {t}. Defaulting to untyped assignement")
        return p_assignment_untyped(p)

    t = loaded_types[t]
    if p[1] not in variables:
        log.debug(f"New variable found {p[1]} of type {t}")
        var = Variable(p[1], t)
        variables[var.name] = var
    else:
        var = variables[p[1]]
        if t != var.type:
            log.warning(f"Variable {var.name} already declared as {var.type}. Cannot convert it as {t}. Leaving it typed as {var.type}.")
    p[0] = Assignment(var, p[3])

def p_assignment_untyped(p):
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
    p2 = p[2]
    p[0] = Expression(p[1], p2)

def p_expression_z3operator2(p):
    'expression : Z3OPERATOR2 expression expression'
    p2 = p[2]
    p3 = p[3]
    p[0] = Expression(p[1], p2, p3)

def p_expression_parens(p):
    'expression : LPAREN expression RPAREN'
    p[0] = p[2]

def p_expression_slice(p):
    'expression : expression LBRACKETS expression COMMA expression RBRACKETS'
    p1 = p[1]
    p3 = p[3]
    p5 = p[5]
    p[0] = Expression('Slice', p1, p3, p5)

def p_expression_indexing(p):
    'expression : expression LBRACKETS expression RBRACKETS'
    p1 = p[1]
    p3 = p[3]
    p[0] = Expression('Index', p1, p3)

def p_expression_struct_access(p):
    'expression : VARIABLE DOT VARIABLE'
    varname = p[1]
    if varname not in variables:
        log.error(f"Unknown varaible {varname}.")
        raise ValueError
    var = variables[p[1]]
    if var.type is None:
        log.error(f"Variable {varname} is untyped. Cannot access sub-fields.")
        raise ValueError
    field = p[3]
    if field not in var.type.fields:
        log.error(f"Variable of type {var.type} does not have any field named {field}")
        raise ValueError
    field_off = var.type.offsets[field]
    field_size = var.type.fields[field].size // 8
    log.debug(f"Struct access: {var}.{field} --> Slice({var}, {field_off}, {field_size}).")
    p[0] = Expression('Slice', Expression("VAR", var), field_off, field_size)

def p_expression_variable(p):
    'expression : VARIABLE'
    log.debug("Found variable " + p[1])
    varname = p[1]
    if varname not in variables:
        log.critical("Using variable %s before assignement" % varname)
        raise NameError
    p[0] = Expression("VAR", variables[varname])

def p_expression_number(p):
    'expression : NUMBER'
    log.debug("Found NUMBER " + str(p[1]))
    p[0] = Expression("IMM", Immediate(p[1]))

def p_expression_string(p):
    'expression : CHAR'
    p[0] = Expression("IMM", Immediate(p[1]))

def p_expression_bool(p):
    'expression : BOOL'
    p[0] = Expression("IMM", BoolImmediate(p[1]))

# Error rule for syntax errors
def p_error(p):
    if p is None:
        return
    log.critical("Syntax error in input! %s" % p)
    raise Exception(p)

try:
    parser = yacc.yacc()
except yacc.YaccError as e:
    log.exception(e)
    sys.exit(1)
