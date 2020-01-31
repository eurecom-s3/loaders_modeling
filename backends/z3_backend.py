from math import log2
import logging
import coloredlogs
from collections import deque

log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)
coloredlogs.install(level="INFO", logger=log)

import z3

from classes import (Base, Immediate, Variable, Expression, Input,
                     Assignment, Condition, Loop)

variables = {}
conditions = {}
terminal_conditions = {}

def SUB(a, b):
    return a - b

def MUL(a, b):
    return a * b

def MOD(a, b):
    return a % b

def DIV(a, b):
    return a / b

def EQ(a, b):
    return a == b

def NEQ(a, b):
    return a != b

def BITOR(a, b):
    return a | b

def BITAND(a, b):
    return a & b

def BITNOT(a):
    return ~a

def ISPOW2(a):
    size = a.size()
    one = z3.BitVecVal(1, size)
    zero = z3.BitVecVal(0, size)
    return (a & (a - one) == zero)

def GE(a, b):
    return a >= b

def LE(a, b):
    return a <= b

def LT(a, b):
    return a < b

def GT(a, b):
    return a > b

def INT(a, b):
    a = a if isinstance(a, int) else a.as_long()
    b = b if isinstance(b, int) else b.as_long()
    return z3.BitVecVal(a, b*8)

def Slice(var, start, cnt=1):
    if isinstance(start, z3.BitVecRef):
        zeroext = z3.ZeroExt(var.size() - start.size(), start)
        shifted = z3.LShR(var, zeroext*8)
        var = shifted
    else:
        shifted = z3.LShR(var, start*8)
        var = shifted

    if isinstance(cnt, z3.BitVecRef):
        cnt = cnt.as_long()
    return z3.Extract((cnt * 8) - 1, 0, var)

def IMM(imm):
    return imm.value if isinstance(imm, Immediate) else imm

def VAR(var):
    return variables[var.name]

z3_funcs = {'ADD'   : z3.Sum,
            'SUB'   : SUB,
            'MUL'   : MUL,
            'DIV'   : DIV,
            'UDIV'  : z3.UDiv,
            'MOD'   : MOD,
            'AND'   : z3.And,
            'OR'    : z3.Or,
            'NOT'   : z3.Not,
            'ULE'   : z3.ULE,
            'UGE'   : z3.UGE,
            'ULT'   : z3.ULT,
            'UGT'   : z3.UGT,
            'EQ'    : EQ,
            'NEQ'   : NEQ,
            'GE'    : GE,
            'LE'    : LE,
            'GT'    : GT,
            'LT'    : LT,
            'BITOR' : BITOR,
            'BITAND': BITAND,
            'BITNOT': BITNOT,
            'Slice' : Slice,
            'Index' : Slice,
            'ISPOW2': ISPOW2,
            'INT'   : INT,
            'VAR'   : VAR,
            'IMM'   : IMM
}

z3_funcs_sized = {'ADD', 'SUB', 'MUL', 'UDIV', 'MOD', 'EQ', 'NEQ', 'GE', 'LE', 'GT', 'LT', 'ULE', 'UGE', 'UGT', 'ULT', 'BITOR', 'BITAND'}
z3_funcs_bool  = {'OR', 'AND', 'NOT'}
z3_funcs_unsigned = {'BITOR', 'BITAND', 'ULE', 'ULT', 'UGT', 'UGE', 'EQ', 'NEQ'}

def dispatch_z3_1(func, arg):
    return z3_funcs[func](arg)

def dispatch_z3_2(func, arg1, arg2):
    if func not in z3_funcs:
        log.critical(f"Function {func} not recognized")
        raise NameError
    if (func in z3_funcs_sized):
        if isinstance(arg1, int):
            arg1 = z3.BitVecVal(arg1, int(log2(2**(arg1.bit_length()+1))))
        if isinstance(arg2, int):
            arg2 = z3.BitVecVal(arg2, int(log2(2**(arg2.bit_length()+1))))
        s1 = arg1.size()
        s2 = arg2.size()
        max_size = max(s1, s2)
        extension_mechanism = (z3.ZeroExt if func in z3_funcs_unsigned
                               else z3.SignExt)
        if s1 != max_size:
            arg1 = extension_mechanism(max_size - s1,
                                       arg1)
        if s2 != max_size:
            arg2 = extension_mechanism(max_size - s2,
                                       arg2)
    return z3_funcs[func](arg1, arg2)

def dispatch_z3_3(func, *args):
    if func != "Slice":
        log.CRITICAL(f"{func} not recognized as a 3-arguments function")
        raise ValueError
    return z3_funcs[func](*args)

def dispatch_z3(func, *args):
    if not 0 < len(args) < 4:
        log.critical(f"Trying to dispatch function with {len(args)}"
                     " arguments")
        raise TypeError
    if len(args) == 1:
        return dispatch_z3_1(func, *args)
    elif len(args) == 2:
        return dispatch_z3_2(func, *args)
    elif len(args) == 3:
        return dispatch_z3_3(func, *args)

dispatch = dispatch_z3

def _eval_expression(expr):
    opcode = expr.opcode
    operands = expr.operands
    operands_new = []
    for op in operands:
        if isinstance(op, Expression):
            operands_new.append(_eval_expression(op))
        else:
            operands_new.append(op)
    return dispatch(opcode, *operands_new)

def _exec_input(stmt):
    variable = stmt.var
    log.debug(f"Creating variable {variable} of size {stmt.size}")
    symb = z3.BitVec(variable.name, stmt.size * 8)
    variables[variable.name] = symb

def _exec_unconditional_assignment(stmt):
    log.debug(f"Executing unconditional assignemnt {stmt}")
    var = stmt.left
    expr = stmt.right
    variables[var.name] = _eval_expression(expr)

def _exec_conditional_assignment(stmt):
    log.debug(f"Executing unconditional assignemnt {stmt}")
    var = stmt.left
    expr = stmt.right
    if var.name not in variables:
        log.warning(f"Variable {var.name} declared in a conditional assignement. Its value in case the condition is not satisfied defaults to 0")

    z3expr = _eval_expression(expr)
    size = z3expr.size()
    variables[var.name] = z3.BitVecVal(0, size)
    variables[var.name] = z3.If(
        z3.And(*[_eval_condition(x) for x in stmt._conditions]),
        z3expr,
        z3.BitVecVal(0, size))

def _exec_assignment(stmt):
    if stmt.conditional:
        return _exec_conditional_assignment(stmt)
    else:
        return _exec_unconditional_assignment(stmt)

def _eval_condition(condition):
    if not condition.conditional:
        return _eval_expression(condition.expr)
    if condition.isterminal:
        return z3.If(
            z3.And(*[_eval_condition(x) for x in condition.conditions]),
            _eval_expression(condition.expr),
            z3.BoolVal(True))

    return z3.And(_eval_expression(condition.expr),
                  *[_eval_condition(x) for x in condition.conditions])

def _exec_condition(stmt):
    conditions[stmt.name] = _eval_condition(stmt)
    if stmt.isterminal:
        terminal_conditions[stmt.name] = conditions[stmt.name]

def _exec_loop(stmt):
    cond_prefix = f"L{stmt._loop_name}_"
    statements = stmt._statements
    ovar = Variable(stmt.output_name)
    ivar = stmt.input_var
    structsize = stmt.structsize
    startpos = stmt.startpos
    count = stmt.count
    for index in range(stmt.maxunroll):
        pref = cond_prefix + f"{index}_"
        log.debug(f"Unrolling loop {stmt}. Index {index}")
        lcond = Condition(Expression("UGT", count, index), False)
        var_assignement = Assignment(ovar,
                                     Expression("Slice", ivar,
                                                Expression("ADD", startpos,
                                                           index*structsize),
                                                structsize),
                                     [lcond])
        _exec_statement(var_assignement)
        for s in statements:
            if isinstance(s, Condition):
                s = s.clone()
                s.add_prefix(pref)
            s._conditions.append(lcond)
            _exec_statement(s)

_exec_table = {Input: _exec_input,
               Assignment: _exec_assignment,
               Condition: _exec_condition,
               Loop: _exec_loop}
def _exec_statement(stmt):
    t = type(stmt)
    log.debug(f"Executing: {stmt}")
    _exec_table[t](stmt)

def exec_statements(statements):
    for stmt in statements:
        _exec_statement(stmt)

def generate_solver():
    log.info("Generating solver")
    solver = z3.Solver()
    for name, condition in terminal_conditions.items():
        solver.assert_and_track(condition, name)
    return solver

def check_sat(solver):
    log.info("Checking satisfiability")
    if solver.check().r != 1:
        log.critical("Model unsatisfiable")
        unsat_core = solver.unsat_core()
        log.critical(f"Unsat core: {unsat_core}")
        for cname in unsat_core:
            log.critical(conditions[str(cname)])
        return None
    else:
        log.info("Model satisfiable")
        log.info("Producing testcase")
        model = solver.model()
        return model

# this routine... if it works it's miracle
def generate_testcase(model):
    log.info("Generating testcase")
    header = variables['HEADER']
    bitvec = model.eval(header)
    string_hex_rev = hex(bitvec.as_long())[2:]
    string_hex_rev = ('0' if (len(string_hex_rev) % 2 == 1) else "") + string_hex_rev
    string_hex = ''.join([string_hex_rev[i:i+2]
                          for i in range(len(string_hex_rev)-2, -2, -2)])
    test = bytes.fromhex(string_hex)
    test += b'\x00' * (header.size() - len(test))
    return test
