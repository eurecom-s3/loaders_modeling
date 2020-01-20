class Statement(object):
    pass

class Base(object):
    def __sub__(self, other):
        return self.symb - other
    def __rsub__(self, other):
        return other - self.symb

class Expression(Base):
    OPCODES = {'VAR'    : 1,
               'IMM'    : 1,
               'ADD'    : 2,
               'SUB'    : 2,
               'MUL'    : 2,
               'UDIV'   : 2,
               'MOD'    : 2,
               'AND'    : 2,
               'OR'     : 2,
               'NOT'    : 1,
               'ULE'    : 2,
               'UGE'    : 2,
               'ULT'    : 2,
               'UGT'    : 2,
               'EQ'     : 2,
               'NEQ'    : 2,
               'GE'     : 2,
               'LE'     : 2,
               'GT'     : 2,
               'LT'     : 2,
               'BITOR'  : 2,
               'BITAND' : 2,
               'BITNOT' : 1,
               'Slice'  : 3,
               'Index'  : 2,
               'ISPOW2' : 1,
               'INT'    : 2,
    }
    def __init__(self, opcode, *operands):
        if opcode not in self.OPCODES:
            raise ValueError(f"Unknown opcode {opcode}")
        self.opcode = opcode
        if len(operands) != self.OPCODES[opcode]:
            raise ValueError(f"Opcode {opcode} expects {self.OPCODES[opcode]}."
                             f"{len(operands)} provided instead.")
        self.operands = operands

    def __repr__(self):
        tmp = f"<Expression ({self.opcode} {self.operands})>"
        return tmp

class Immediate(object):
    def __init__(self, value):
        self.value = value

    def __repr__(self):
        return f"<Immediate {self.value}>"

class BoolImmediate(Immediate):
    def __init__(self, value):
        if not isinstance(value, bool):
            t = type(expr)
            raise TypeError(f"expr must be of type bool. {t} found instead")
        self.value = value


class Variable(object):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return f"<Variable {self.name}>"

class Input(Statement):
    def __init__(self, var, size):
        self.var = var
        self.size = size

    def __repr__(self):
        s = f"<Input {self.var} {self.size} bytes>"
        return s

class Assignment(Statement):
    def __init__(self, left, right, conditions=list()):
        if not isinstance(left, Variable):
            t = type(left)
            raise TypeError(f"Left operand of an "
                            f"assignment must be a variable. "
                            f"It is {t} instead")
        self.left = left

        if not isinstance(right, Expression):
            t = type(right)
            raise TypeError(f"Right operand of an "
                            f"assignment must be an expression. "
                            f"It is {t} instead")
        self.right = right

        if not isinstance(conditions, list):
            t = type(conditions)
            raise TypeError(f"Conditions must be a list. "
                            f"It is {t} instead")
        if not all(isinstance(Condition, x) for x in conditions):
            raise TypeError("Conditions must be a list of Condition object")
        self._conditions = conditions

    def __repr__(self):
        s = f"<Assignment {self.left} <- {self.right}"
        if len(self.conditions) != 0:
            s += f" if {self._conditions}>"
        return s

    @property
    def conditions(self):
        return self._conditions
    @conditions.setter
    def conditions(self, new):
        if not isinstance(new, list):
            t = type(new)
            raise TypeError(f"Conditions must be a list. "
                            f"It is {t} instead")
        if not all(isinstance(x, Condition) for x in new):
            raise TypeError("Conditions must be a list of Condition object")
        self._conditions = new
    @property
    def conditional(self):
        return len(self._conditions) != 0

    # def apply(self):
    #     if not self.conditional:
    #         self.left.symb = self.right.symb
    #     else:
    #         newexpr = z3.If(z3.And(*[x.model for x in self._conditions]),
    #                         self.right.symb, self.left.symb)
    #         self.left.symb = newexpr

class Loop(Statement):
    def __init__(self, loop_name, output_name, input_var, startpos, structsize, count, maxunroll):
        self._loop_name = loop_name
        self.output_name = output_name
        if not isinstance(input_var, Expression):
            t = type(input_var)
            raise TypeError(f"Expected Expression for input_var."
                            f"Found {t}")
        self.input_var = input_var

        if not isinstance(startpos, Expression):
            t = type(start_pos)
            raise TypeError(f"Expected Expression for start_pos."
                            f"Found {t}")
        self.startpos = startpos

        if not isinstance(count, Expression):
            t = type(count)
            raise TypeError(f"Expected Expression for count."
                            f"Found {t}")
        self.count = count

        self.maxunroll = maxunroll
        self.structsize = structsize
        self._statements = []

    def add_statement(self, stmt):
        if not isinstance(stmt, Statement):
            t = type(stmt)
            raise TypeError(f"Expected Statement for stmt"
                            f"Found {t} instead")
        self._statements.append(stmt)

    def __repr__(self):
        s = f"<Loop {self._loop_name}: {self.output_name} in {self.input_var}>"
        return s

class Condition(Statement):
    def __init__(self, expr, isterminal, conditions=list()):
        if isinstance(expr, Expression):
            self.expr = expr
        elif isinstance(expr, bool):
            self.expr = Expression("IMM", expr)
        else:
            raise TypeError
        self.isterminal = bool(isterminal)

        if not isinstance(conditions, list):
            t = type(conditions)
            raise TypeError(f"Conditions must be a list. "
                            f"It is {t} instead")
        if not all(isinstance(x, Condition) for x in conditions):
            raise TypeError("Conditions must be a list of Condition object")
        self._conditions = conditions
        self.name = None

    @property
    def conditions(self):
        return self._conditions
    @conditions.setter
    def conditions(self, new):
        if not isinstance(new, list):
            t = type(new)
            raise TypeError(f"Conditions must be a list. "
                            f"It is {t} instead")
        if not all(isinstance(x, Condition) for x in new):
            raise TypeError("Conditions must be a list of Condition object")
        self._conditions = new
    @property
    def conditional(self):
        return len(self._conditions) != 0

    # @property
    # def model(self):
    #     if not self.conditional:
    #         return self.expr.symb

    #     if self.isterminal:
    #         return z3.If(z3.And(*[x.model for x in self.conditions]),
    #                      self.expr.symb,
    #                      z3.BoolVal(True))
    #     return z3.And(self.expr.symb, *[x.model for x in self.conditions])

    def __repr__(self):
        s = "<"
        s += "Terminal " if self.isterminal else ""
        s += f"Condition {self.expr}"
        if len(self.conditions) != 0:
            s += f" if {self._conditions}>"
        return s

    def __invert__(self):
        return Condition(Expression("NOT", self.expr), self.isterminal,
                         self._conditions)

class ConditionListEntry(Base):
    def __init__(self, name, negated=False):
        self.name = name
        self.negated = negated

    def __add__(self, other):
        if isinstance(other, ConditionList):
            return ConditionList([self, *other.l])
        elif isinstance(other, ConditionListEntry):
            return ConditionList([self, other])
        else:
            t = type(other)
            raise TypeError(f"other must be either a ConditionList or a ConditionListEntry"
                            f"It is {t} instead")
    def __repr__(self):
        return self.name

class ConditionList(Base):
    def __init__(self, l):
        if not isinstance(l, list):
            t = type(l)
            raise TypeError(f"l must be a list. It is {t} instead")
        if not all(isinstance(x, ConditionListEntry) for x in l):
            raise TypeError("All elements of l must be of type ConditionListEntry")

        self.l = l

    @property
    def names(self):
        return [x.name for x in self.l]

    def __iadd__(self, other):
        if isinstance(other, ConditionList):
            self.l += other.l
        elif isinstance(other, ConditionListEntry):
            self.l += [other]
        else:
            t = type(other)
            raise TypeError(f"other must be either a ConditionList or a ConditionListEntry"
                            f"It is {t} instead")
        return self

    def __add__(self, other):
        if isinstance(other, ConditionList):
            return ConditionList(self.l + other.l)
        elif isinstance(other, ConditionListEntry):
            return ConditionList(self.l + [other])
        else:
            t = type(other)
            raise TypeError(f"other must be either a ConditionList or a ConditionListEntry"
                            f"It is {t} instead")

    def __repr__(self):
        s = "[" + ', '.join(str(x) for x in self.l) + ']'
        return s

    def __iter__(self):
        return self.l.__iter__()
