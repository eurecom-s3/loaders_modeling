#!/usr/bin/env python3
import logging
import z3

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class ConditionalLoopTest(Test):
    testfile = "tests/loops/conditionalloop.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(ConditionalLoopTest.testfile)

        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        testcase = backend.generate_testcase()
        expected = b'\x01' * 4
        assert(testcase[4:8] == expected)

if __name__ == "__main__":
    ConditionalLoopTest.run()
