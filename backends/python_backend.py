from math import log2
import logging
import coloredlogs
from collections import deque

log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)
coloredlogs.install(level="INFO", logger=log)

from pwnlib.util.packing import pack, unpack

from classes import (Base, Immediate, Variable, Expression, Input,
                     Assignment, Condition, Loop)

def sized(skipargs=(), skipret=False):
    def sized_outer(func):
        def sized_inner(*args):
            targs = [x for n, x in enumerate(args) if n not in skipargs]
            max_size = max(len(x) for x in targs)
            args = [x + b'\x00'*(max_size - len(x)) for x in targs]
            ret = func(*args)
            if not skipret:
                start = len(ret) - max_size
            return ret if skipret else ret[start:]
        return sized_inner
    return sized_outer

def unsigned(skipargs=(), skipret=False):
    def unsigned_outer(func, *skip):
        def unsigned_inner(*args):
            # unpack the argumts as unsigned (unless they are ignored)
            args = [unpack(x, 'all', endianness='little', sign=False)
                    if n not in skipargs else x for n, x in enumerate(args)]
            ret = func(*args)
            return ret if skipret else pack(ret, 'all',
                                            endianness='little', sign=False)
        return unsigned_inner
    return unsigned_outer

def signed(skipargs=(), skipret=False):
    def signed_outer(func, *skip):
        def signed_inner(*args):
            args = [unpack(x, 'all', endianness='little', sign=True)
                    if n not in skipargs else x for n, x in enumerate(args)]
            ret = func(*args)
            return ret if skipret else pack(ret, 'all',
                                            endianness='little', sign=True)
        return signed_inner
    return signed_outer

class VerificationError(Exception):
    def __init__(self, name):
        self.name = name

class PythonBackend():
    def __init__(self):
        self.variables = {}
        self.conditions = {}
        self.terminal_conditions = {}
        self._statements = None
        self.funcs = { 'ADD'   : self.ADD,
                       'SUB'   : self.SUB,
                       'MUL'   : self.MUL,
                       'DIV'   : self.DIV,
                       'UDIV'  : self.UDIV,
                       'MOD'   : self.MOD,
                       'AND'   : self.And,
                       'OR'    : self.Or,
                       'NOT'   : self.Not,
                       'ULE'   : self.ULE,
                       'UGE'   : self.UGE,
                       'ULT'   : self.ULT,
                       'UGT'   : self.UGT,
                       'EQ'    : self.EQ,
                       'NEQ'   : self.NEQ,
                       'GE'    : self.GE,
                       'LE'    : self.LE,
                       'GT'    : self.GT,
                       'LT'    : self.LT,
                       'BITOR' : self.BITOR,
                       'BITAND': self.BITAND,
                       'BITNOT': self.BITNOT,
                       'Slice' : self.Slice,
                       'Index' : self.Slice,
                       'ISPOW2': self.ISPOW2,
                       'INT'   : self.INT,
                       'VAR'   : self.VAR,
                       'IMM'   : self.IMM
        }

    @staticmethod
    @sized()
    @signed()
    def ADD(a, b):
        return a + b

    @staticmethod
    @sized()
    @signed()
    def SUB(a, b):
        return a - b

    @staticmethod
    @sized()
    @signed()
    def MUL(a, b):
        return a * b

    @staticmethod
    @sized()
    @signed()
    def MOD(a, b):
        return a % b

    @staticmethod
    @sized()
    @signed()
    def DIV(a, b):
        return a // b

    @staticmethod
    @sized()
    @unsigned()
    def UDIV(a, b):
        return a // b

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def EQ(a, b):
        return a == b

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def NEQ(a, b):
        return a != b

    @staticmethod
    @sized()
    @unsigned()
    def BITOR(a, b):
        return a | b

    @staticmethod
    @sized()
    @unsigned()
    def BITAND(a, b):
        return a & b

    @staticmethod
    @sized()
    @unsigned()
    def BITNOT(a):
        return ~a

    @staticmethod
    @unsigned()
    def ISPOW2(a):
        return (a == 0) or (a & (a - 1)) == 0

    @staticmethod
    def And(a, b):
        return a and b

    @staticmethod
    def Or(a, b):
        return a or b

    @staticmethod
    def Not(a):
        return not a

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def ULE(a, b):
        return a <= b

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def UGE(a, b):
        return a >= b

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def ULT(a, b):
        return a < b

    @staticmethod
    @sized(skipret=True)
    @unsigned(skipret=True)
    def UGT(a, b):
        return a > b

    @staticmethod
    @sized(skipret=True)
    @signed(skipret=True)
    def GE(a, b):
        return a >= b

    @staticmethod
    @sized(skipret=True)
    @signed(skipret=True)
    def LE(a, b):
        return a <= b

    @staticmethod
    @sized(skipret=True)
    @signed(skipret=True)
    def LT(a, b):
        return a < b

    @staticmethod
    @sized(skipret=True)
    @signed(skipret=True)
    def GT(a, b):
        return a > b

    @staticmethod
    def INT(a, b):
        return pack(a, b*8, endianness="little")

    @staticmethod
    @unsigned(skipargs=(0, ), skipret=True)
    def Slice(var, start, cnt=1):
        if cnt == 1:
            # Indexing a b-string in python returns an int...
            return pack(var[start], 'all')
        else:
            return var[start:start+cnt]

    @staticmethod
    def IMM(imm):
        val = imm.value if isinstance(imm, Immediate) else imm
        return pack(val, 'all', endianness='little')

    def VAR(self, var):
        return self.variables[var.name]

    funcs_bool  = {'OR', 'AND', 'NOT'}
    funcs_unsigned = {'BITOR', 'BITAND', 'ULE', 'ULT', 'UGT', 'UGE', 'EQ', 'NEQ'}

    def dispatch(self, func, *args):
        if not 0 < len(args) < 4:
            log.critical(f"Trying to dispatch function with {len(args)}"
                         " arguments")
            raise TypeError
        ret = self.funcs[func](*args)
        return ret

    def _eval_expression(self, expr):
        log.debug(f"Evaluating expression {expr}")
        opcode = expr.opcode
        operands = expr.operands
        operands_new = []
        for op in operands:
            if isinstance(op, Expression):
                operands_new.append(self._eval_expression(op))
            else:
                operands_new.append(op)
        return self.dispatch(opcode, *operands_new)

    def _exec_input(self, stmt):
        # variable = stmt.var
        # log.debug(f"Creating variable {variable} of size {stmt.size}")
        # symb = pack(0, stmt.size * 8, endianness='little')
        # self.variables[variable.name] = symb
        pass

    def _exec_unconditional_assignment(self, stmt):
        left = stmt.left.name
        rigth = stmt.right
        self.variables[left] = self._eval_expression(rigth)

    def _exec_conditional_assignment(self, stmt):
        left = stmt.left.name
        rigth = stmt.right
        conditions = stmt.conditions
        if left not in self.variables:
            log.warning(f"Variable {left} initialized in conditional statement. Defaulting it to 0.")
            self.variables[left] = pack(0, "all")

        if all(self._eval_condition(x) for x in conditions):
            self.variables[left] = self._eval_expression(rigth)

    def _exec_assignment(self, stmt):
        if stmt.conditional:
            return self._exec_conditional_assignment(stmt)
        else:
            return self._exec_unconditional_assignment(stmt)

    def _eval_condition(self, condition):
        if condition.name and condition.name in self.conditions:
            return self.conditions[condition.name]
        expr = self._eval_expression(condition.expr)
        conds = all(self._eval_condition(x)
                    for x in condition.conditions)
        if condition.isterminal:
            if conds:
                return expr
            else:
                return True
        return expr & conds

    def _exec_condition(self, stmt):
        name = stmt.name
        if name is None:
            log.warning("Executing unnamed condition... Not sure this is intended.")
        res = self._eval_condition(stmt)
        self.conditions[name] = res

        if not res and stmt.isterminal:
            log.critical(f"Terminal condition {name} not met. Verification failed")
            raise VerificationError(name)

    def _exec_loop(self, stmt):
        name = f"L{stmt._loop_name}"
        varname = Variable(stmt.output_name)
        inputvar = stmt.input_var
        startpos = stmt.startpos
        count = unpack(self._eval_expression(stmt.count), 'all',
                       endianness='little')
        structsize = Expression("IMM", Immediate(stmt.structsize))

        log.debug(f"Executing loop {name} {count} times")
        for iteration in range(count):
            conditionpref = f"{name}_{iteration}_"
            iterationexpr = Expression("IMM", Immediate(iteration))
            nstartpos = Expression("ADD", startpos,
                                  Expression("MUL", structsize, iterationexpr))
            sliceexpr = Expression("Slice", inputvar, nstartpos, structsize)
            assignment = Assignment(varname, sliceexpr)
            self._exec_assignment(assignment)
            for s in stmt._statements:
                if isinstance(s, Condition):
                    s = s.clone()
                    s.add_prefix(conditionpref)
                self._exec_statement(s)

    _exec_table = {Input: _exec_input,
                   Assignment: _exec_assignment,
                   Condition: _exec_condition,
                   Loop: _exec_loop}

    def _exec_statement(self, stmt):
        t = type(stmt)
        log.debug(f"Executing: {stmt}")
        self._exec_table[t](self, stmt)

    def load_statements(self, statements):
        self._statements = statements

    def verify(self, test, variable="HEADER"):
        if not self._statements:
            log.error("Load statements before call verify()")
            raise ValueError

        self.variables[variable] = test
        for stmt in self._statements:
            try:
                self._exec_statement(stmt)
            except VerificationError as e:
                log.error(f"Condition {e.name} not satisfied. "
                          "Verification failed.")
                return False
        return True

if __name__ == "__main__":
    inp = Input(Variable("input"), 64)
    bcknd = PythonBackend()
    bcknd._exec_input(inp)
    expr = Expression("EQ",
                      Expression("ADD",
                                 Expression("VAR", Variable("input")),
                                 Expression("IMM", 8)),
                      Expression("IMM", 8))
    res1 = bcknd._eval_expression(expr)
