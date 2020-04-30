from math import log2
import logging
import coloredlogs
from collections import deque

import z3

from .default_backend import DefaultBackend
from classes import (Base, Immediate, Variable, Expression, Input,
                     Assignment, Condition, Loop, VLoop, Optimization,
                     Optimizations)

class Z3Backend(DefaultBackend):
    def __init__(self, name="", voi=None, enable_optimizations=False):
        super().__init__()
        self.name = name
        self.voi = voi
        self._solver = None
        self._model = None
        self.z3_funcs = { 'ADD'       : z3.Sum,
                          'SUB'       : self.SUB,
                          'MUL'       : self.MUL,
                          'DIV'       : self.DIV,
                          'UDIV'      : z3.UDiv,
                          'MOD'       : self.MOD,
                          'AND'       : z3.And,
                          'OR'        : z3.Or,
                          'NOT'       : z3.Not,
                          'ULE'       : z3.ULE,
                          'UGE'       : z3.UGE,
                          'ULT'       : z3.ULT,
                          'UGT'       : z3.UGT,
                          'EQ'        : self.EQ,
                          'NEQ'       : self.NEQ,
                          'GE'        : self.GE,
                          'LE'        : self.LE,
                          'GT'        : self.GT,
                          'LT'        : self.LT,
                          'BITOR'     : self.BITOR,
                          'BITAND'    : self.BITAND,
                          'BITNOT'    : self.BITNOT,
                          'SHR'       : self.SHR,
                          'SHL'       : self.SHL,
                          'Slice'     : self.Slice,
                          'Index'     : self.Slice,
                          'ISPOW2'    : self.ISPOW2,
                          'ALIGNUP'   : self.ALIGNUP,
                          'ALIGNDOWN' : self.ALIGNDOWN,
                          'INT'       : self.INT,
                          'VAR'       : self.VAR,
                          'IMM'       : self.IMM
        }
        self.enable_optimizations = enable_optimizations
        self.optimizations = []
        self.log = logging.getLogger(__name__)
        self.log.setLevel(logging.DEBUG)
        coloredlogs.install(level="INFO", logger=self.log)


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
        return a / b

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
    def SHR(a, b):
        return a >> b

    @staticmethod
    def SHL(a, b):
        return a << b

    @staticmethod
    def ISPOW2(a):
        size = a.size()
        one = z3.BitVecVal(1, size)
        zero = z3.BitVecVal(0, size)
        return (a & (a - one) == zero)

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
    def ALIGNUP(a, b):
        return (a + b - 1) & -b

    @staticmethod
    def ALIGNDOWN(a, b):
        return a & -b

    @staticmethod
    def INT(a, b):
        a = a if isinstance(a, int) else a.as_long()
        b = b if isinstance(b, int) else b.as_long()
        return z3.BitVecVal(a, b*8)

    @staticmethod
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

    @staticmethod
    def IMM(imm):
        return imm.value if isinstance(imm, Immediate) else imm

    def VAR(self, var):
        return self.variables[var.name]

    z3_funcs_sized = {'ADD', 'SUB', 'MUL', 'UDIV', 'MOD', 'EQ', 'NEQ', 'GE', 'LE', 'GT', 'LT', 'ULE', 'UGE', 'UGT', 'ULT', 'BITOR', 'BITAND', 'ALIGNUP', 'ALIGNDOWN'}
    z3_funcs_bool  = {'OR', 'AND', 'NOT'}
    z3_funcs_unsigned = {'ADD', 'SUB', 'BITOR', 'BITAND', 'ULE', 'ULT', 'UGT', 'UGE', 'EQ', 'NEQ'}

    def dispatch_z3_1(self, func, arg):
        return self.z3_funcs[func](arg)

    def dispatch_z3_2(self, func, arg1, arg2):
        if func not in self.z3_funcs:
            self.log.critical(f"Function {func} not recognized")
            raise NameError
        if (func in self.z3_funcs_sized):
            if isinstance(arg1, int):
                arg1 = z3.BitVecVal(arg1, int(log2(2**(arg1.bit_length()+1))))
            if isinstance(arg2, int):
                arg2 = z3.BitVecVal(arg2, int(log2(2**(arg2.bit_length()+1))))
            s1 = arg1.size()
            s2 = arg2.size()
            max_size = max(s1, s2)
            extension_mechanism = (z3.ZeroExt if func in self.z3_funcs_unsigned
                                   else z3.SignExt)
            if s1 != max_size:
                arg1 = extension_mechanism(max_size - s1,
                                           arg1)
            if s2 != max_size:
                arg2 = extension_mechanism(max_size - s2,
                                           arg2)
        return self.z3_funcs[func](arg1, arg2)

    def dispatch_z3_3(self, func, *args):
        if func != "Slice":
            self.log.CRITICAL(f"{func} not recognized as a 3-arguments function")
            raise ValueError
        return self.z3_funcs[func](*args)

    def dispatch_z3(self, func, *args):
        if not 0 < len(args) < 4:
            self.log.critical(f"Trying to dispatch function with {len(args)}"
                         " arguments")
            raise TypeError
        if len(args) == 1:
            return self.dispatch_z3_1(func, *args)
        elif len(args) == 2:
            return self.dispatch_z3_2(func, *args)
        elif len(args) == 3:
            return self.dispatch_z3_3(func, *args)

    dispatch = dispatch_z3

    def _exec_input(self, stmt):
        variable = stmt.var
        self.log.debug(f"Creating variable {variable} of size {stmt.size}")
        symb = z3.BitVec(variable.name, stmt.size * 8)
        self.variables[variable.name] = symb

    def _exec_unconditional_assignment(self, stmt):
        self.log.debug(f"Executing unconditional assignemnt {stmt}")
        var = stmt.left
        expr = stmt.right
        self.variables[var.name] = self._eval_expression(expr)

    def _exec_conditional_assignment(self, stmt):
        self.log.debug(f"Executing unconditional assignemnt {stmt}")
        var = stmt.left
        expr = stmt.right
        z3expr = self._eval_expression(expr)
        size = z3expr.size()

        if var.name not in self.variables:
            self.log.warning(f"Variable {var.name} declared in a conditional assignement. Its value in case the condition is not satisfied defaults to 0")
            self.variables[var.name] = z3.BitVecVal(0, size)

        self.variables[var.name] = z3.If(
            self._eval_condition_list(stmt._conditions),
            z3expr,
            self.variables[var.name])

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
                self._eval_condition_list(condition.conditions),
                self._eval_expression(condition.expr),
                z3.BoolVal(True))

        return z3.And(self._eval_expression(condition.expr),
                      self._eval_condition_list(condition.conditions))

    def _eval_condition_list(self, conditions):
        return z3.And(*[self._eval_condition(x) for x in conditions])

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
        conditions = stmt._conditions
        for index in range(stmt.maxunroll):
            pref = cond_prefix + f"{index}_"
            self.log.debug(f"Unrolling loop {stmt}. Index {index}")
            lcond = Condition(Expression("UGT", count, Expression("IMM", Immediate(index))), False)
            var_assignement = Assignment(ovar,
                                         Expression("Slice", ivar,
                                                    Expression("ADD", startpos,
                                                               Expression("IMM", Immediate(index*structsize))),
                                                    Expression("IMM", Immediate(structsize))),
                                         [*conditions, lcond])
            self._exec_statement(var_assignement)
            for s in statements:
                if isinstance(s, Condition):
                    s = s.clone()
                    s.add_prefix(pref)
                s._conditions.extend(conditions)
                s._conditions.append(lcond)
                self._exec_statement(s)

    def _exec_vloop(self, stmt):
        cond_prefix = f"L{stmt._loop_name}_"
        statements = stmt._statements
        ovar = Variable(stmt.output_name)
        start = stmt.start
        nextvar = stmt.nextname
        condname = stmt.contcondition
        maxunroll = stmt.maxunroll
        conditions = stmt._conditions

        if condname in self.conditions:
            cond = self.conditions[condname]
        else:
            cond = Condition(True, isterminal=False, name=condname)
            self.conditions[condname] = cond

        # Assign the first value
        initial_assignement = Assignment(ovar, start, [*conditions])
        self._exec_assignment(initial_assignement)
        # Unroll
        for index in range(stmt.maxunroll):
            # Prefix for the conditions
            pref = cond_prefix + f"{index}_"
            self.log.debug(f"Unrolling loop {stmt}. Index {index}")

            # For each statement in the loop
            for s in statements:
                # if the statement is a condition...
                if isinstance(s, Condition):
                    # ... clone it
                    s = s.clone()
                    # if it changes the loop condition...
                    if s.name == condname:
                        # keep it in mind for later
                        nextcond = s
                    # change its name, adding the prefix
                    s.add_prefix(pref)
                s._conditions.extend([*conditions, cond])
                self._exec_statement(s)

            cond = nextcond
            nextcond = None
            nextassignment = Assignment(ovar, Expression("VAR", nextvar),
                                        conditions=[*conditions, cond])
            self._exec_assignment(nextassignment)

    def _exec_optimization(self, stmt):
        strategy = stmt.strategy
        expression = stmt.expression
        if strategy in (Optimizations.MAXIMIZE, Optimizations.MINIMIZE):
            self.enable_optimizations = True
            self.optimizations.append((strategy,
                                       self._eval_expression(expression)))
        else:
            log.error(f"Strategy {stmt.strategy} not implemented")
            raise NotImplementedError

    _exec_table = {Input: _exec_input,
                   Assignment: _exec_assignment,
                   Condition: _exec_condition,
                   Loop: _exec_loop,
                   VLoop: _exec_vloop,
                   Optimization: _exec_optimization
    }

    def generate_solver(self):
        if self.enable_optimizations:
            return self.generate_optimizer()
        self.log.info("Generating solver")
        solver = z3.Solver()
        for name, condition in self.terminal_conditions.items():
            solver.assert_and_track(condition, name)
        self._solver = solver
        return solver

    def generate_optimizer(self):
        self.log.info("Generating optimizer")
        solver = z3.Optimize()
        for name, condition in self.terminal_conditions.items():
            solver.assert_and_track(condition, name)
        for strategy, expression in self.optimizations:
            if strategy == Optimizations.MAXIMIZE:
                solver.maximize(expression)
            elif strategy == Optimizations.MINIMIZE:
                solver.minimize(expression)
        self._solver = solver
        return solver

    @property
    def solver(self):
        if self._solver is None:
            self.generate_solver()
        return self._solver

    def check_sat(self):
        solver = self.solver
        self.log.info("Checking satisfiability")
        if solver.check().r != 1:
            self.log.critical("Model unsatisfiable")
            unsat_core = solver.unsat_core()
            self.log.critical(f"Unsat core: {unsat_core}")
            for cname in unsat_core:
                self.log.critical(self.conditions[str(cname)])
            return None
        else:
            self.log.info("Model satisfiable")
            model = solver.model()
            self._model = model
            return model

    @property
    def model(self):
        if self._model is None:
            self.check_sat()
        return self._model

    # this routine... if it works it's miracle
    def generate_testcase(self, varname="HEADER"):
        model = self.model
        self.log.info("Generating testcase")
        header = self.variables[varname]
        bitvec = model.eval(header)
        string_hex_rev = hex(bitvec.as_long())[2:]
        string_hex_rev = ('0' if (len(string_hex_rev) % 2 == 1) else "") + string_hex_rev
        string_hex = ''.join([string_hex_rev[i:i+2]
                              for i in range(len(string_hex_rev)-2, -2, -2)])
        test = bytes.fromhex(string_hex)
        test += b'\x00' * (int(header.size()/8) - len(test))
        return test

    def verify(self, test, variable="HEADER"):
        if not self._statements:
            self.log.error("Load statements before call verify()")
            raise ValueError
        self.exec_statements(self._statements)

        var = self.variables[variable]
        size = var.size()
        if len(test) > size:
            self.log.critical("The file to verify is bigger than the input of the model. Aborting.")
            raise ValueError
        test += b'\x00' * (size - len(test))
        testvec = z3.BitVecVal(int.from_bytes(test, "little"), size*8)
        self.variables['TEST__'] = testvec
        expr = Expression("EQ", Expression("VAR", Variable(variable)), Expression("VAR", Variable("TEST__")))
        constraint = Condition(expr, True, name='VTEST')
        self._exec_statement(constraint)
        self.generate_solver()
        return self.check_sat()

    def __and__(self, other):
        if other.voi != self.voi:
            log.error("Variable of interest (voi) differs in the two models")
        ret = Z3Backend(name=f"{self.name}&{other.name}", voi=self.voi)

        for condname, cond in self.terminal_conditions.items():
            ret.terminal_conditions[f"{self.name}_{condname}"] = cond
        for condname, cond in other.terminal_conditions.items():
            ret.terminal_conditions[f"{other.name}_{condname}"] = cond

        ret.variables[f'{self.name}_{ret.voi}'] = self.variables[ret.voi]
        ret.variables[f'{other.name}_{ret.voi}'] = other.variables[ret.voi]
        ret.variables[f'{ret.voi}'] = self.variables[ret.voi]
        voicond = Condition(
            Expression("EQ",
                       Expression("VAR", Variable(f'{self.name}_{ret.voi}')),
                       Expression("VAR", Variable(f'{other.name}_{ret.voi}')),
            ),
            isterminal=True, name="voicond")
        ret._exec_condition(voicond)
        return ret

    def __invert__(self):
        ret = Z3Backend(name=f"~{self.name}", voi=self.voi)
        ret.variables[f'{ret.voi}'] = self.variables[ret.voi]
        conditions = []
        for condname, cond in self.terminal_conditions.items():
            ncond = z3.Not(cond)
            conditions.append(ncond)
        ret.terminal_conditions['negated'] = z3.Or(conditions)
        return ret
