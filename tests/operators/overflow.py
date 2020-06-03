#!/usr/bin/env python3

import logging
import z3

from modelLang import parsers, backends

from modelLang.parsers import Parser
from modelLang.backends import Z3Backend

class OverflowTest():
    testfile = "tests/operators/overflow.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(OverflowTest.testfile)
        backend = Z3Backend()
        backend.log.setLevel(logging.ERROR)
        backend.exec_statements(parser.statements)
        solver = backend.generate_solver()
        variables = backend.variables

        ### Check sat
        assert(backend.model)

        model = backend.model
        var4 = model.eval(variables['VAR4']).as_long()
        var5 = model.eval(variables['VAR5']).as_long()
        assert(var4 + var5 >= 0x100000000)
