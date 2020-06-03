#!/usr/bin/env python3
import logging
import z3

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class VLoopTest(Test):
    testfile = "tests/loops/vloop.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(VLoopTest.testfile)

        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        testcase = backend.generate_testcase()
        expected = b''.join([x.to_bytes(1, 'little') for x in range(0x10)])
        assert testcase[:0x10] == expected, "First part of the testcase not as expected"
        assert all(x == 0 for x in testcase[0x10:]), "Second part of the testcase not as expected"
        return True

if __name__ == "__main__":
    VLoopTest.run()
