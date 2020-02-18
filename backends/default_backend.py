from classes import Expression

class DefaultBackend(object):
    def __init__(self):
        self.variables = {}
        self.conditions = {}
        self.terminal_conditions = {}
        self._statements = None

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

    def _exec_statement(self, stmt):
        t = type(stmt)
        self.log.debug(f"Executing: {stmt}")
        self._exec_table[t](self, stmt)

    def exec_statements(self, statements):
        for stmt in statements:
            self._exec_statement(stmt)

    def load_statements(self, statements):
        self._statements = statements

class VerificationError(Exception):
    def __init__(self, name):
        self.name = name
