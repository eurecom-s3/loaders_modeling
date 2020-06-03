#!/usr/bin/env python3
import logging
import z3

from modelLang import parsers, backends

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

from pwnlib.util.packing import unpack

class PositiveCombinationTest():
    testfile1 = "tests/functional/mod1.lmod"
    testfile2 = "tests/functional/mod2.lmod"

    @staticmethod
    def run():
        parser1 = Parser()
        parser1.parse_file(PositiveCombinationTest.testfile1)

        backend1 = Z3Backend(name=PositiveCombinationTest.testfile1,
                             voi="variable")
        backend1.log.setLevel(logging.ERROR)
        backend1.exec_statements(parser1.statements)

        parser2 = Parser()
        parser2.parse_file(PositiveCombinationTest.testfile2)

        backend2 = Z3Backend(name=PositiveCombinationTest.testfile2,
                             voi="variable")
        backend2.log.setLevel(logging.ERROR)
        backend2.exec_statements(parser2.statements)

        backend = backend1 & backend2
        backend.log.setLevel(logging.ERROR)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        testcase = backend.generate_testcase("variable")
        testcase = unpack(testcase, 'all')
        assert(testcase > 15)
        assert(testcase & 0xffff == 0)
        assert((testcase & (testcase - 1) != 0))
        return True

if __name__ == "__main__":
    PositiveCombinationTest.run()
