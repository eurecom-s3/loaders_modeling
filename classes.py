import z3

class Base(object):
    def __sub__(self, other):
        return self.symb - other
    def __rsub__(self, other):
        return other - self.symb

class Expression(Base):
    def __init__(self, expr):
        self.expr = expr

    @property
    def symb(self):
        if isinstance(self.expr, Variable):
            return self.expr.symb
        else:
            return self.expr

    def __repr__(self):
        tmp = f"<Expression {self.expr.__repr__()}>"
        return " ".join(tmp.split())

    @property
    def size(self):
        size = self.symb.size
        return size() if callable(size) else size

class Immediate(Expression):
    def __init__(self, expr):
        self.expr = expr
        self._symb = None

    @property
    def size(self):
        return max(self.expr.bit_length(), 8)

    def __repr__(self):
        return f"<Immediate {self.expr}>"

    @property
    def symb(self):
        if not self._symb:
            self._symb = z3.BitVecVal(self.expr, self.size)
        return self._symb

class Variable(Base):
    def __init__(self, name, symb=None):
        self.name = name
        self._symb = symb

    def __repr__(self):
        return f"<Variable {self.name}>"

    @property
    def symb(self):
        if isinstance(self._symb, Expression):
            return self._symb.symb
        else:
            return self._symb
    @symb.setter
    def symb(self, new):
        self._symb = new

    @property
    def size(self):
        size = self.symb.size
        return size() if callable(size) else size

class Assignment(object):
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
        s = f"<Assignement {self.left} <- {self.right}"
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

    def apply(self):
        if not self.conditional:
            self.left.symb = self.right.symb
        else:
            newexpr = z3.If(z3.And(*[x.model for x in self._conditions]),
                            self.right.symb, self.left.symb)
            self.left.symb = newexpr

class Condition(object):
    def __init__(self, expr, isterminal, conditions=list()):
        if isinstance(expr, Expression):
            self.expr = expr
        elif isinstance(expr, bool):
            self.expr = Expression(z3.BoolVal(expr))
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

    @property
    def model(self):
        if not self.conditional:
            return self.expr.symb

        if self.isterminal:
            return z3.If(z3.And(*[x.model for x in self.conditions]),
                         self.expr.symb,
                         z3.BoolVal(True))
        return z3.And(self.expr.symb, *[x.model for x in self.conditions])

    def __repr__(self):
        s = "<"
        s += "Terminal " if self.isterminal else ""
        s += f"Condition {self.expr}"
        if len(self.conditions) != 0:
            s += f" if {self._conditions}>"
        return s
