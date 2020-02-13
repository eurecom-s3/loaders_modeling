from math import log2
import logging
import coloredlogs
from collections import deque

log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)
coloredlogs.install(level="INFO", logger=log)

from classes import (Base, Immediate, Variable, Expression, Input,
                     Assignment, Condition, Loop)

class PythonBackend():
    def __init__(self):
        self.variables = {}
        self.conditions = {}
        self.terminal_conditions = {}
        self.funcs = { 'ADD'   : self.ADD,
                       'SUB'   : self.SUB,
                       'MUL'   : self.MUL,
                       'DIV'   : self.DIV,
                       'UDIV'  : self.UDiv,
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
    def ADD(a, b):
        return a + b

    @staticmethod
    def SUB(a, b):
        return a - b

    @staticmethod
    def MUL(a, b):
        return a * b

    @staticmethod
    def MOD(a, b):
        return a % b

    @staticmethod
    def DIV(a, b):
        return a // b

    @staticmethod
    def UDIV(a, b):
        return a // b

    @staticmethod
    def EQ(a, b):
        return a == b

    @staticmethod
    def NEQ(a, b):
        return a != b

    @staticmethod
    def BITOR(a, b):
        return a | b

    @staticmethod
    def BITAND(a, b):
        return a & b

    @staticmethod
    def BITNOT(a):
        return ~a

    @staticmethod
    def ISPOW2(a):
        return (a == 0) || (a & (a - 1)) == 0

    @staticmethod
    def And(a, b):
        return a && b

    @staticmethod
    def Or(a, b):
        return a || b

    @staticmethod
    def Not(a, b):
        return !a

    @staticmethod
    def ULE(a, b):
        return a <= b

    @staticmethod
    def UGE(a, b):
        return a >= b

    @staticmethod
    def ULT(a, b):
        return a < b

    @staticmethod
    def UGT(a, b):
        return a > b

    @staticmethod
    def GE(a, b):
        return a >= b

    @staticmethod
    def LE(a, b):
        return a <= b

    @staticmethod
    def LT(a, b):
        return a < b

    @staticmethod
    def GT(a, b):
        return a > b

    @staticmethod
    def INT(a, b):
        return a

    @staticmethod
    def Slice(var, start, cnt=1):
        if cnt == 1:
            return var[start]
        else:
            return var[start:start+cnt]

    @staticmethod
    def IMM(imm):
        return imm.value if isinstance(imm, Immediate) else imm

    def VAR(self, var):
        return self.variables[var.name]

    funcs_bool  = {'OR', 'AND', 'NOT'}
    funcs_unsigned = {'BITOR', 'BITAND', 'ULE', 'ULT', 'UGT', 'UGE', 'EQ', 'NEQ'}

    def dispatch(self, func, *args):
        if not 0 < len(args) < 4:
            log.critical(f"Trying to dispatch function with {len(args)}"
                         " arguments")
            raise TypeError
        return self.funcs[func](*args)

    def _eval_expression(self, expr):
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
        variable = stmt.var
        log.debug(f"Creating variable {variable} of size {stmt.size}")
        self.variables[variable.name] = symb

    def _exec_unconditional_assignment(self, stmt):
        log.debug(f"Executing unconditional assignemnt {stmt}")
        var = stmt.left
        expr = stmt.right
        self.variables[var.name] = self._eval_expression(expr)

    def _exec_conditional_assignment(self, stmt):
        log.debug(f"Executing unconditional assignemnt {stmt}")
        var = stmt.left
        expr = stmt.right
        if var.name not in self.variables:
            log.warning(f"Variable {var.name} declared in a conditional assignement. Its value in case the condition is not satisfied defaults to 0")

        z3expr = self._eval_expression(expr)
        size = z3expr.size()
        self.variables[var.name] = z3.BitVecVal(0, size)
        self.variables[var.name] = z3.If(
            z3.And(*[self._eval_condition(x) for x in stmt._conditions]),
            z3expr,
            z3.BitVecVal(0, size))

    def _exec_assignment(self, stmt):
        if stmt.conditional:
            return self._exec_conditional_assignment(stmt)
        else:
            return self._exec_unconditional_assignment(stmt)

    def _eval_condition(self, condition):
        if not condition.conditional:
            return self._eval_expression(condition.expr)
        if condition.isterminal:
            return z3.If(
                z3.And(*[self._eval_condition(x) for x in condition.conditions]),
                self._eval_expression(condition.expr),
                z3.BoolVal(True))

        return z3.And(self._eval_expression(condition.expr),
                      *[self._eval_condition(x) for x in condition.conditions])

    def _exec_condition(self, stmt):
        self.conditions[stmt.name] = self._eval_condition(stmt)
        if stmt.isterminal:
            self.terminal_conditions[stmt.name] = self.conditions[stmt.name]

    def _exec_loop(self, stmt):
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
            self._exec_statement(var_assignement)
            for s in statements:
                if isinstance(s, Condition):
                    s = s.clone()
                    s.add_prefix(pref)
                s._conditions.append(lcond)
                self._exec_statement(s)

    _exec_table = {Input: _exec_input,
                   Assignment: _exec_assignment,
                   Condition: _exec_condition,
                   Loop: _exec_loop}

    def _exec_statement(self, stmt):
        t = type(stmt)
        log.debug(f"Executing: {stmt}")
        self._exec_table[t](self, stmt)

    def exec_statements(self, statements):
        for stmt in statements:
            self._exec_statement(stmt)

    def generate_solver(self):
        log.info("Generating solver")
        solver = z3.Solver()
        for name, condition in self.terminal_conditions.items():
            solver.assert_and_track(condition, name)
        self._solver = solver
        return solver

    @property
    def solver(self):
        if self._solver is None:
            self.generate_solver()
        return self._solver

    def check_sat(self):
        solver = self.solver
        log.info("Checking satisfiability")
        if solver.check().r != 1:
            log.critical("Model unsatisfiable")
            unsat_core = solver.unsat_core()
            log.critical(f"Unsat core: {unsat_core}")
            for cname in unsat_core:
                log.critical(self.conditions[str(cname)])
            return None
        else:
            log.info("Model satisfiable")
            log.info("Producing testcase")
            model = solver.model()
            self._model = model
            return model

    @property
    def model(self):
        if self._model is None:
            self.check_sat()
        return self._model

    # this routine... if it works it's miracle
    def generate_testcase(self):
        model = self.model
        log.info("Generating testcase")
        header = self.variables['HEADER']
        bitvec = model.eval(header)
        string_hex_rev = hex(bitvec.as_long())[2:]
        string_hex_rev = ('0' if (len(string_hex_rev) % 2 == 1) else "") + string_hex_rev
        string_hex = ''.join([string_hex_rev[i:i+2]
                              for i in range(len(string_hex_rev)-2, -2, -2)])
        test = bytes.fromhex(string_hex)
        test += b'\x00' * (header.size() - len(test))
        return test
