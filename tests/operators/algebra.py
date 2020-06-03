#!/usr/bin/env python3

import logging
import z3

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class AlgebraTest(Test):
    testfile = "tests/operators/algebra.mod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(AlgebraTest.testfile)
        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        variables = backend.variables
        input = variables['VARIABLE']
        v1 = variables['VARA']
        v2 = variables['VARB']
        v3 = variables['VARC']
        v4 = variables['VARD']
        v5 = variables['VARE']
        v6 = variables['VARF']

        solver.add(input == 10)
        assert(solver.check() == z3.sat)
        model = solver.model()
        assert(model.eval(v1).as_long() == 15)
        assert(model.eval(v2).as_long() == 5)
        assert(model.eval(v3).as_long() == 50)
        assert(model.eval(v4).as_long() == 2)
        assert(model.eval(v5).as_long() == 2)
        assert(model.eval(v6).as_long() == 0)
