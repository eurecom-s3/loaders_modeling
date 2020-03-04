#!/usr/bin/env python3

import logging
import os.path

from tests import Test
from parsers import Parser
from backends import Z3Backend

from pwnlib.util.packing import pack, unpack

class OptimizationTest(Test):
    testfile = "tests/statements/optimization.lmod"

    @staticmethod
    def run():
        parser = Parser(pwd=os.path.dirname(os.path.realpath(__file__)))
        parser.parse_file(OptimizationTest.testfile)

        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        var1 = backend.generate_testcase(varname="var1")
        var2 = backend.generate_testcase(varname="var2")
        var1 = unpack(var1, 'all', endianness="little")
        var2 = unpack(var2, 'all', endianness="little")
        assert var1 == var2 == 10

        return True

if __name__ == "__main__":
    OptimizationTest.run()
