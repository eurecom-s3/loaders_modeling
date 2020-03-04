#!/usr/bin/env python3
import z3

from tests import Test
from parsers import Parser
from backends import *


class AlignmentTest(Test):
    testfile = "tests/operators/alignment.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(AlignmentTest.testfile)
        backend = Z3Backend()
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        assert(solver.check() == z3.sat)

if __name__ == "__main__":
    AlignmentTest.run()
