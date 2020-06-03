#!/usr/bin/env python3
import z3
import logging

from modelLang import parsers, backends

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class StringCompareTest():
    testfile = "tests/operators/strcmp.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(StringCompareTest.testfile)
        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        assert(solver.check() == z3.sat)
        model = solver.model()
        outvar = backend.variables['out']
        assert(model.eval(outvar).as_long() == 0x5241424f4f4600)

if __name__ == "__main__":
    StringCompareTest.run()
