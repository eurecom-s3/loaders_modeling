class Expression(object):
    def __init__(self, expr):
        self.expr = expr

class Variable(object):
    def __init__(self, name, dimension=None, symb=None):
        self.name = name
        self.dimension = dimension
        self.symb = symb

    def __repr__(self):
        return f"{self.name} {self.dimension} bytes"

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

class Condition(object):
    def __init__(self, expr, isterminal):
        if not isinstance(expr, Expression):
            raise TypeError
        self.expr = expr
        self.isterminal = bool(isterminal)
