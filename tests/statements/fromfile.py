#!/usr/bin/env python3

import logging
import os.path

from modelLang import parsers, backends
from tests import Test

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend
class FromFileTest(Test):
    testfile = "tests/statements/fromfile.lmod"

    @staticmethod
    def run():
        parser = Parser(pwd=os.path.dirname(os.path.realpath(__file__)))
        parser.parse_file(FromFileTest.testfile)

        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.solver
        model = backend.model

        assert model, "Model unsat. Test failed"

        testcase = backend.generate_testcase(varname="file")
        assert(testcase[5:5+10] == b"1337133713")

        return True

if __name__ == "__main__":
    FromFileTest.run()
