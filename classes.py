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
    def __init__(self, left, right):
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
    def __repr__(self):
        return f"<Assignement {self.left} <- {self.right}>"

    def apply(self):
        self.left.symb = self.right.symb

class Condition(object):
    def __init__(self, expr, isterminal):
        if not isinstance(expr, Expression):
            raise TypeError
        self.expr = expr
        self.isterminal = bool(isterminal)
