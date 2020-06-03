#!/usr/bin/env python3

import logging
import z3

from modelLang import parsers, backends

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend


class BitwiseTest():
    testfile = "tests/operators/bitwise.mod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(BitwiseTest.testfile)
        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        input = backend.variables['VARIABLE']
        v1 = backend.variables['VARA']
        v2 = backend.variables['VARB']
        v3 = backend.variables['VARC']

        solver.add(input == 0xdeadbeef)
        assert(solver.check() == z3.sat)
        model = solver.model()
        assert(model.eval(v1).as_long() == 0x11001)
        assert(model.eval(v2).as_long() == 0xdfadbeef)
        assert(model.eval(v3).as_long() == 0x21524110)

if __name__ == "__main__":
    BitwiseTest.run()
