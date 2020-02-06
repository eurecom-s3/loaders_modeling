import sys
import logging
import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from parsers import Parser
from backends import *

ftestcase = "testcase"

def write_testcase(testcase):
    with open(ftestcase, "wb") as fp:
        fp.write(testcase)

def parse_pe():
    pe = pefile.PE(ftestcase)
    return pe

if __name__ == "__main__":
    modelfile = sys.argv[1]
    parser = Parser()
    parser.parse_file(modelfile)
    exec_statements(parser.statements)
    solver = generate_solver()
    model = check_sat(solver)
    if model:
        testcase = generate_testcase(model)
        write_testcase(testcase)
        pefile = parse_pe()
