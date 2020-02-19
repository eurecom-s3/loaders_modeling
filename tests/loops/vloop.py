#!/usr/bin/env python3
import z3

from tests import Test
from parsers import Parser
from backends import Z3Backend

def parse_file(f):
    lines = f.readlines()
    cnt = 0
    for s in lines:
        cnt += 1
        if not s: continue
        log.info(f"Line {cnt}: {s}")
        result = parser.parse(s)
        if result:
            print(result)

class VLoopTest(Test):
    testfile = "tests/loops/vloop.lmod"

    @staticmethod
    def run():
        parser = Parser()
        parser.parse_file(VLoopTest.testfile)

        backend = Z3Backend()
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
