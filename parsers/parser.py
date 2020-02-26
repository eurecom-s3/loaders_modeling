import sys
import os.path
import logging
import pickle
from collections import deque, defaultdict
from utils import customdefdict

import coloredlogs

log = logging.getLogger(__name__)
log.setLevel(10)
coloredlogs.install(level="INFO", logger=log)

import ply.yacc as yacc

# Get the token map from the lexer.  This is required.
from .langlex import Lexer
from classes import Variable, Assignment, Expression, Condition, Immediate, BoolImmediate, ConditionList, ConditionListEntry, Loop, VLoop, Input, Define, Optimization, Optimizations

def read_file(filename):
    with open(filename, "rb") as fp:
        buf = fp.read()
        return buf

class Parser:
    tokens = Lexer.tokens
    def parse_file(self, fname):
        self._fname = fname
        self._cwd = os.path.dirname(fname)
        with open(fname, "r") as f:
            lines = f.readlines()
            cnt = 0
            for s in lines:
                cnt += 1
                if not s: continue
                log.debug(f"Line {cnt}: {s}")
                result = self.parser.parse(s)
                if result:
                    print(result)

    @property
    def variables(self):
        return self._variables

    @property
    def statements(self):
        return self._statements

    @property
    def conditions(self):
        return self._conditions

    @property
    def defines(self):
        return self._defines

    def p_input(self, p):
        'input : input NEWLINE'
        p[0] = p[1]

    def p_input_ass(self, p):
        'input : assignment_stmt'
        log.debug("Assignment: " + str(p[1]))
        if len(self._block_stack) == 0:
            self.statements.append(p[1])
        else:
            block = self._block_stack.pop()
            block.add_statement(p[1])
            self._block_stack.append(block)

    def p_input_cond(self, p):
        'input : condition_stmt'
        log.debug("Condition " + str(p[1]))
        name, condition = p[1]
        self.conditions[name.upper()] = condition
        condition.name = name.upper()
        if len(self._block_stack) == 0:
            self.statements.append(condition)
        else:
            block = self._block_stack.pop()
            block.add_statement(condition)
            self._block_stack.append(block)

    def p_input_input(self, p):
        'input : input_stmt'
        log.debug("Input " + str(p[1]))
        stmt = Input(p[1][0], p[1][1])
        self.statements.append(stmt)
        self.variables[p[1][0].name] = p[1][0]

    def p_input_loopstart(self, p):
        'input : loopstart_stmt'
        log.debug("Loop start " + str(p[1]))
        loop = p[1][1]
        self._block_stack.append(loop)
        var = self.variables[loop.output_name]
        var.type = loop.vtype

    def p_input_loopend(self, p):
        'input : loopend_stmt'
        loop = self._block_stack.pop()
        if loop._loop_name != p[1][0]:
            log.critical("Loop end does not match current loop name")
            raise ValueError
        log.debug("Loop end " + str(p[1][0]))
        self.statements.append(loop)

    def p_input_define(self, p):
        'input : define_stmt'
        stmt = p[1]
        if stmt.name in self.variables:
            log.warning(f"Defining constant {stmt.name}, but a variable with the same name already declared. Skipping")
        else:
            self.defines[stmt.name] = stmt.value

    def p_input_optimize(self, p):
        'input : OPTIMIZE expression'
        strategy = p[1]
        expression = p[2]
        opt = Optimization(strategy, expression)
        self.statements.append(opt)

    def p_input_fromfile(self, p):
        'input : FROMFILE VARIABLE expression expression NUMBER NUMBER'
        filename = os.path.join(self.pwd, p[2])
        symbol = p[3]
        start = p[4]
        foffset = p[5]
        nbytes = p[6]
        buf = read_file(filename)
        for n, b in enumerate(buf[foffset:foffset+nbytes]):
            curroffset = Expression("ADD", start, Expression("IMM", Immediate(n)))
            nb = Expression("Index", symbol, curroffset)
            expr = Expression("EQ", nb, Expression("IMM", Immediate(b)))
            cond = Condition(expr, isterminal=True, name=f"FROM_{filename}_{n}")
            self.statements.append(cond)
            self.conditions[cond.name] = cond

    def p_define_stmt(self, p):
        'define_stmt : DEFINE VARIABLE expression'
        p[0] = Define(p[2], p[3])

    def p_input_load(self, p):
        'input : load_stmt'
        use_cwd = p[1][2]
        os = p[1][1]
        header = p[1][0]
        module_name = 'structures.' + (os if os != "DEFAULT" else "cparser")
        module = __import__(module_name, globals(), locals(), ['parse_file'])
        dirpath = self._cwd if use_cwd else "structures/headers"
        header_file = dirpath + f"/{header}.h"
        with open(header_file, "r") as fp:
            fcontent = fp.read()

        new_types = module.parse_file(fcontent)
        new_defs = module.preprocess_defs(fcontent)
        self.loaded_types.update(new_types[1])
        new_defs = {x: Expression("IMM", y) for x, y in new_defs.items()}
        self.defines.update(new_defs)

    def p_load_stmt(self, p):
        'load_stmt : LOADTYPES VARIABLE VARIABLE'
        if p[3] == 'linux':
            os = 'DEFAULT'
        else:
            os = p[3]
        p[0] = (p[2], os, p[1])

    def p_load_stmt_2(self, p):
        'load_stmt : LOADTYPES VARIABLE'
        p[0] = (p[2], "DEFAULT", p[1])

    def p_input_stmt_type(self, p):
        'input_stmt : INPUT VARIABLE constant TYPE VARIABLE'
        log.debug("Input statement")
        t = p[5]
        if t not in self.loaded_types:
            log.warning(f"Unknown type {t}. Defaulting to untyped variable")
            var = (Variable(p[2]), p[3])
        else:
            var = (Variable(p[2], self.loaded_types[t]), p[3])
        p[0] = var

    def p_input_stmt(self, p):
        'input_stmt : INPUT VARIABLE constant'
        log.debug("Input statement")
        var = (Variable(p[2]), p[3])
        p[0] = var

    def p_constant_number(self, p):
        'constant : NUMBER'
        p[0] = p[1]

    def p_constant_define(self, p):
        'constant : VARIABLE'
        name = p[1]
        if name not in self.defines:
            log.error(f"{name} not defined as a constant")
            raise ValueError
        p[0] = self.defines[name].operands[0].value

    def p_assignment_stmt_uncond(self, p):
        'assignment_stmt : ASSIGNSTART COLON assignment'
        assignment = p[3]
        p[0] = assignment

    def p_assignment_stmt_cond(self, p):
        'assignment_stmt : ASSIGNSTART conditionlist COLON assignment'
        assignement = p[4]
        assignement.left.symb = assignement.right
        conditionslist = p[2]
        conds = [~self.conditions[c.name] if c.negated else
                 self.conditions[c.name]
                 for c in conditionslist]
        assignement.conditions = conds
        p[0] = assignement

    def p_condition_stmt_uncond(self, p):
        'condition_stmt : CONDITIONNAME COLON conditionexpr'
        p[3].name = p[1]
        p[0] = (p[1], p[3])

    def p_condition_stmt_cond(self, p):
        'condition_stmt : CONDITIONNAME conditionlist COLON conditionexpr'
        cond = p[4]
        cond.name = p[1]
        conditionslist = p[2]
        conds = [self.conditions[c] for c in conditionslist.names]
        cond.conditions = conds
        p[0] = (p[1], cond)

    def p_condition_stmt_noexpr(self, p):
        'condition_stmt : CONDITIONNAME conditionlist SEMICOLON'
        conditionslist = p[2]
        conds = [self.conditions[c] for c in conditionslist.names]
        cond = Condition(True, False, conds)
        p[0] = (p[1], cond)

    def p_loopstart_stmt_typed(self, p):
        '''loopstart_stmt : loopstart TYPE VARIABLE
                            | vloopstart TYPE VARIABLE'''
        t = p[3]
        if t not in self.loaded_types:
            raise TypeError(f"Unknown type {t}")
        loop = p[1]
        loop[1].vtype = self.loaded_types[t]
        p[0] = loop

    def p_loopstart_stmt_untyped(self, p):
        '''loopstart_stmt : loopstart
                            | vloopstart'''
        p[0] = p[1]

    def p_loopstart_stmt(self, p):
        'loopstart : LOOPSTART COLON VARIABLE ARROW LOOP LPAREN expression COMMA expression COMMA NUMBER COMMA expression COMMA NUMBER RPAREN'
        loopindex = p[1]
        loop = Loop(p[1], p[3], p[7], p[9], p[11], p[13], p[15])
        p[0] = (loopindex, loop)

    def p_loopstart_stmt_2(self, p):
        'loopstart : LOOPSTART COLON VARIABLE ARROW LOOP LPAREN expression COMMA expression COMMA expression COMMA expression COMMA NUMBER RPAREN'
        loopindex = p[1]
        structsize = p[11]
        if structsize.opcode != "IMM":
            raise ValueError("Struct size must be a number")
        structsize = structsize.operands[0].value
        loop = Loop(p[1], p[3], p[7], p[9], structsize, p[13], p[15])
        p[0] = (loopindex, loop)

    def p_vloopstart_stmt_variable(self, p):
        'vloopstart : LOOPSTART COLON VARIABLE ARROW VLOOP LPAREN expression COMMA VARIABLE COMMA CONDITIONNAME COMMA NUMBER RPAREN'
        loopindex = p[1]
        newvar = p[3]
        start = p[7]
        nextname = Variable(p[9])
        condition = p[11]
        maxunroll = p[13]
        loop = VLoop(loopindex, newvar, start, nextname, condition, maxunroll)
        p[0] = (loopindex, loop)

    def p_loopend_stmt(self, p):
        'loopend_stmt : LOOPEND'
        p[0] = (p[1], )

    def p_assignment_typed(self, p):
        'assignment : VARIABLE ARROW expression TYPE VARIABLE'
        var = None
        t = p[5]
        if t not in self.loaded_types:
            log.warning(f"Unknown type {t}. Defaulting to untyped assignement")
            return p_assignment_untyped(self, p)

        t = self.loaded_types[t]
        if p[1] not in self.variables:
            log.debug(f"New variable found {p[1]} of type {t}")
            var = Variable(p[1], t)
            self.variables[var.name] = var
        else:
            var = self.variables[p[1]]
            if t != var.type:
                log.warning(f"Variable {var.name} already declared as {var.type}. Cannot convert it as {t}. Leaving it typed as {var.type}.")
        p[0] = Assignment(var, p[3])

    def p_assignment_untyped(self, p):
        'assignment : VARIABLE ARROW expression'
        var = None
        if p[1] not in self.variables:
            log.debug(f"New variable found {p[1]}")
            var = Variable(p[1])
            self.variables[var.name] = var
        else:
            var = self.variables[p[1]]
        p[0] = Assignment(var, p[3])

    def p_conditionlist(self, p):
        '''conditionlist : LPAREN conditionlistint RPAREN'''
        p[0] = p[2]

    def p_conditionlistint_1(self, p):
        'conditionlistint : conditionlistentry'
        p[0] = ConditionList([p[1]])

    def p_conditionlistint_2(self, p):
        'conditionlistint : conditionlistint COMMA conditionlistentry'
        p[0] = p[1] + p[3]

    def p_conditionlistentry_negcondition(self, p):
        'conditionlistentry : EXCLAMATION CONDITIONNAME'
        p[0] = ConditionListEntry(p[2], False)

    def p_conditionlistentry_condition(self, p):
        'conditionlistentry : CONDITIONNAME'
        p[0] = ConditionListEntry(p[1], True)

    def p_condition_terminal(self, p):
        'conditionexpr : expression TERMINATOR'
        p[0] = Condition(p[1], True)

    def p_condition_normal(self, p):
        'conditionexpr : expression'
        p[0] = Condition(p[1], False)

    def p_expression_z3operator1(self, p):
        'expression : OPERATOR1 expression'
        p2 = p[2]
        p[0] = Expression(p[1], p2)

    def p_expression_z3operator2(self, p):
        'expression : OPERATOR2 expression expression'
        p2 = p[2]
        p3 = p[3]
        p[0] = Expression(p[1], p2, p3)

    def p_expression_parens(self, p):
        'expression : LPAREN expression RPAREN'
        p[0] = p[2]

    def p_expression_slice(self, p):
        'expression : expression LBRACKETS expression COMMA expression RBRACKETS'
        p1 = p[1]
        p3 = p[3]
        p5 = p[5]
        p[0] = Expression('Slice', p1, p3, p5)

    def p_expression_indexing(self, p):
        'expression : expression LBRACKETS expression RBRACKETS'
        p1 = p[1]
        p3 = p[3]
        p[0] = Expression('Index', p1, p3)

    def p_expression_struct_access(self, p):
        'expression : VARIABLE DOT VARIABLE'
        varname = p[1]
        if varname not in self.variables:
            log.error(f"Unknown varaible {varname}.")
            raise ValueError
        var = self.variables[p[1]]
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
        p[0] = Expression('Slice', Expression("VAR", var),
                          Expression("IMM", Immediate(field_off)),
                          Expression("IMM", Immediate(field_size)))

    def p_expression_sizeof(self, p):
        'expression : SIZEOF VARIABLE'
        typename = p[2]
        if typename not in self.loaded_types:
            raise TypeError(f"Unknown type {typename}")
        size = self.loaded_types[typename].size // 8
        p[0] = Expression("IMM", Immediate(size))

    def p_expression_variable(self, p):
        'expression : VARIABLE'
        log.debug("Found variable " + p[1])
        varname = p[1]
        if varname not in self.variables and varname not in self.defines:
            log.critical("Using variable %s before assignement" % varname)
            raise NameError

        if varname in self.variables:
            p[0] = Expression("VAR", self.variables[varname])
        else:
            p[0] = self.defines[varname]

    def p_expression_number(self, p):
        'expression : NUMBER'
        log.debug("Found NUMBER " + str(p[1]))
        p[0] = Expression("IMM", Immediate(p[1]))

    def p_expression_string(self, p):
        'expression : CHAR'
        p[0] = Expression("IMM", Immediate(p[1]))

    def p_expression_bool(self, p):
        'expression : BOOL'
        p[0] = Expression("IMM", BoolImmediate(p[1]))

    # Error rule for syntax errors
    def p_error(self, p):
        if p is None:
            return
        log.critical("Syntax error in input! %s" % p)
        raise Exception(p)

    def __init__(self, pwd=""):
        self.lexer = Lexer()
        self.loaded_types = {}
        self._variables = customdefdict(lambda x: Variable(x))
        self._conditions = {}
        self._defines = {}
        self._block_stack = deque()
        self._statements = []
        self.pwd = pwd
        try:
            self.parser = yacc.yacc(module=self)
        except yacc.YaccError as e:
            log.exception(e)
            sys.exit(1)
