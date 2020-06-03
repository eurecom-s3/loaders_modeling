#!/usr/bin/env python3

import logging
import os.path

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

from pwnlib.util.packing import pack, unpack

class ConditionalAssignmentTest(Test):
    testfile = "tests/statements/conditional_assignment.lmod"

    @staticmethod
    def run():
        parser = Parser(pwd=os.path.dirname(os.path.realpath(__file__)))
        parser.parse_file(ConditionalAssignmentTest.testfile)

        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        outvar = backend.generate_testcase(varname="outvar")
        outvar = unpack(outvar, 'all', endianness="little")
        assert outvar == 0x1234

        return True

if __name__ == "__main__":
    ConditionalAssignmentTest.run()
