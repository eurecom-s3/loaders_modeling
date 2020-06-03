#!/usr/bin/env python3
import z3
import logging

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class AlignmentTest(Test):
    testfile = "tests/operators/alignment.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(AlignmentTest.testfile)
        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        assert(solver.check() == z3.sat)

if __name__ == "__main__":
    AlignmentTest.run()
