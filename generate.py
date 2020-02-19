#!/usr/bin/env python3
import sys
import logging
import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from parsers import Parser
from backends import Z3Backend

ftestcase = "testcase"

def write_testcase(testcase):
    with open(ftestcase, "wb") as fp:
        fp.write(testcase)

if __name__ == "__main__":
    modelfile = sys.argv[1]
    parser = Parser()
    parser.parse_file(modelfile)
    backend = Z3Backend()
    backend.exec_statements(parser.statements)
    solver = backend.solver
    model = backend.model
    if model:
        testcase = backend.generate_testcase()
        write_testcase(testcase)
